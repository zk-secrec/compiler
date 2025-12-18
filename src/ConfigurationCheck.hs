{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveTraversable #-}
module ConfigurationCheck (checkConfiguration, typeIxs, RCon(..), MainRing(..), TestData(..)) where


import Control.Lens
import Control.Monad (when)
import Control.Monad.IO.Class
import Data.Maybe (isNothing, isJust, mapMaybe)
import Data.List (findIndices, group, sort, sortOn, partition)
import qualified Data.IntMap as IM (IntMap, fromList, (!))
import qualified Data.Map as M (Map, (!), fromList)
import qualified Data.Text as T (Text)

import Basic.Name (Name, mainFName)
import Basic.Var (Var, varName, tyVarKind)
import Basic.Location
import CCC.Checks (checkFieldPreds, checkBitwisePreds)
import CCC.Syntax (Versioned(..), CCC(..), CCCType(..), CCCChallenge(..), CCCConversion(..), CCCPlugin(..))
import Support.Pretty (Pretty(..), Doc, render, (<+>), ($$), vcat, viaShow, parens)
import Support.UniqMap (UniqMap, fromListUM, findUM, adjustUM)
import Support.Unique (Uniquable)
import Typing.Type
import Typing.Typing (TypedProgram(..), TypedDefault(..), findFunType)

import CompilerException


data RCon
  = Plain
  | Bitwise
  deriving (Show, Eq, Ord)
data MainTypeArg
  = Known Integer
  | Unknown Name
  deriving (Eq)
data MainRing a
  = MR
    { _rcon :: RCon
    , _arg  :: a
    }
  deriving (Eq, Ord, Functor, Foldable, Traversable)

data TestData
  = TestData
    { _supportedRings      :: [MainRing Integer]   -- rings that are needed in the program and supported by CCC
    , _supportedChallenges :: [MainRing Integer]   -- rings where challenges are needed in the program and supported by CCC
    , _supportedConverts   :: [(MainRing Integer , MainRing Integer)] -- ring pairs between which conversions are needed in the program and supported by CCC
    , _supportedPlugins    :: [[Versioned T.Text]] -- plugins that are needed in the program and supported by CCC
                                                   -- grouped by plugin families differing by version only
                                                   -- increasingly sorted by version in each family
    , _mainTypeParamsEval  :: UniqMap (Located Integer) -- evaluation of the type parameters of the main function
    }
data PredData
  = PredData
    { _types      :: [Located (MainRing MainTypeArg)]
    , _challenges :: [Located (MainRing MainTypeArg)]
    , _converts   :: [Located (MainRing MainTypeArg, MainRing MainTypeArg)]
    , _plugins    :: [Located T.Text]
    }
data MainPred
  = MainPred
    { _assumed :: PredData
    , _tested  :: PredData
    }

makeLenses ''PredData
makeLenses ''MainPred

emptyPredData
  :: PredData
emptyPredData
  = PredData
    { _types      = []
    , _challenges = []
    , _converts   = []
    , _plugins    = []
    }


instance Pretty MainTypeArg where
  
  pretty (Known n)
    = "Known" <+> pretty n
  pretty (Unknown x)
    = "Unknown" <+> pretty x
  

instance (Pretty a) => Pretty (MainRing a) where
  
  pretty mr
    = "MR" <+> viaShow (_rcon mr) <+> parens (pretty (_arg mr))
  

checkPreds
  :: MainRing Integer -> Located (CCCType a) -> Bool
checkPreds mr
  = case _rcon mr of
      Plain
        -> checkFieldPreds (_arg mr)
      _ -> checkBitwisePreds (_arg mr)

findMainRing
  :: RingType Var -> Maybe (MainRing MainTypeArg)
findMainRing t
  = let
      outer
        = case t of
            TPlain _
              -> Just Plain
            TBitwise _
              -> Just Bitwise
            _ -> Nothing
      inner
        = do
            nat <- natOfRing t
            case nat of
              (TNat (Finite n))
                -> Just (Known (toInteger n))
              (TVar var _ _)
                -> Just (Unknown (varName var))
              _ -> Nothing
    in
    MR <$> outer <*> inner

lookupKnown
  :: MainTypeArg -> Maybe Integer
lookupKnown (Known n)
  = Just n
lookupKnown _
  = Nothing

lookupUnknown
  :: MainTypeArg -> Maybe Name
lookupUnknown (Unknown x)
  = Just x
lookupUnknown _
  = Nothing

isKnown
  :: MainTypeArg -> Bool
isKnown
  = isJust . lookupKnown

sortWithoutRep
  :: (Ord a)
  => [a] -> [a]
sortWithoutRep
  = fmap head . group . sort

sortWithoutRepOn
  :: (Eq a, Ord b)
  => (a -> b) -> [a] -> [a]
sortWithoutRepOn f
  = fmap head . group . sortOn f

collectAll
  :: (Ord a)
  => (MainTypeArg -> Maybe a) -> MainPred -> [Located (MainRing a)]
collectAll lookup mp
  = let
      find preddata
        = let
            types = mapMaybe (traverse (traverse lookup)) $ _types preddata
            challenges = mapMaybe (traverse (traverse lookup)) $ _challenges preddata
            converts = mapMaybe (traverse (traverse lookup)) . fmap noLoc . uncurry (++) . unzip . fmap unLocated $ _converts preddata
          in
          types ++ challenges ++ converts
    in
    sortWithoutRepOn unLocated $ find (_assumed mp) ++ find (_tested mp)

collectTypes
  :: (MainTypeArg -> Maybe a) -> PredData -> [Located (MainRing a)]
collectTypes lookup preddata
  = mapMaybe (traverse (traverse lookup)) $ _types preddata

collectChallenges
  :: (MainTypeArg -> Maybe a) -> PredData -> [Located (MainRing a)]
collectChallenges lookup preddata
  = mapMaybe (traverse (traverse lookup)) $ _challenges preddata

collectConverts
  :: (MainTypeArg -> Maybe a) -> PredData -> [Located (MainRing a , MainRing a)]
collectConverts lookup preddata
  = mapMaybe (traverse (\ (x , y) -> (,) <$> traverse lookup x <*> traverse lookup y)) $ _converts preddata

collectConvertFromKnowns
  :: (MainTypeArg -> Maybe a) -> PredData -> [Located (MainRing Integer , MainRing a)]
collectConvertFromKnowns lookup preddata
  = mapMaybe (traverse (\ (x , y) -> (,) <$> traverse lookupKnown x <*> traverse lookup y)) $
    filter (isKnown . _arg . fst . unLocated) $ 
    _converts preddata

collectConvertToKnowns
  :: (MainTypeArg -> Maybe a) -> PredData -> [Located (MainRing a , MainRing Integer)]
collectConvertToKnowns lookup preddata
  = mapMaybe (traverse (\ (x , y) -> (,) <$> traverse lookup x <*> traverse lookupKnown y)) $
    filter (isKnown . _arg . snd . unLocated) $ 
    _converts preddata

classifyPredicates
  :: [TypePred Var] -> (MainPred, [TypePred Var])
classifyPredicates
  = let
      op pred (mainpred , otherpred)
        = case pred of
            PredPostRing t l
              | Just mr <- findMainRing t
                -> (mainpred & assumed . types %~ (Located l mr :) , otherpred)
            PredPostConvertible t1 t2 l
              | Just mr1 <- findMainRing t1, Just mr2 <- findMainRing t2
                -> (mainpred & assumed . converts %~ (Located l (mr1 , mr2) :) , otherpred)
            PredChallenge t l
              | Just mr <- findMainRing t
                -> (mainpred & assumed . challenges %~ (Located l mr :) , otherpred)
            PredExtendedArithmetic l
              -> (mainpred & assumed . plugins %~ (Located l "extended_arithmetic" :) , otherpred)
            PredPermutationCheck l
              -> (mainpred & assumed . plugins %~ (Located l "permutation_check" :) , otherpred)
            PredVectors l
              -> (mainpred & assumed . plugins %~ (Located l "vectors" :) , otherpred)
            PredVectorization l
              -> (mainpred & assumed . plugins %~ (Located l "iter" :) , otherpred)
            PredObliviousChoice l
              -> (mainpred & assumed . plugins %~ (Located l "disjunction" :) , otherpred)
            PredTestPostRing t l
              | Just mr <- findMainRing t
                -> (mainpred & tested . types %~ (Located l mr :) , otherpred)
            PredTestPostConvertible t1 t2 l
              | Just mr1 <- findMainRing t1, Just mr2 <- findMainRing t2
                -> (mainpred & tested . converts %~ (Located l (mr1 , mr2) :) , otherpred)
            PredTestChallenge t l
              | Just mr <- findMainRing t
                -> (mainpred & tested . challenges %~ (Located l mr :) , otherpred)
            PredTestExtendedArithmetic l
              -> (mainpred & tested . plugins %~ (Located l "extended_arithmetic" :) , otherpred)
            PredTestPermutationCheck l
              -> (mainpred & tested . plugins %~ (Located l "permutation_check" :) , otherpred)
            PredTestVectors l
              -> (mainpred & tested . plugins %~ (Located l "vectors" :) , otherpred)
            PredTestObliviousChoice l
              -> (mainpred & tested . plugins %~ (Located l "disjunction" :) , otherpred)
            _ -> (mainpred, pred : otherpred)
      e = (MainPred { _assumed = emptyPredData, _tested = emptyPredData }, [])
    in
    foldr op e

typeIxs
  :: Located (MainRing Integer) -> [Located (CCCType T.Text)] -> Located [Int]
typeIxs (Located l mr) lfamilies
  = Located l (findIndices (checkPreds mr) lfamilies)

typeMap
  :: [Located (MainRing Integer)] -> [Located (CCCType T.Text)] -> M.Map (MainRing Integer) (Located [Int]) 
  -- the values are lists of indices of CCC types embracing the key type, along with the ZKSC file location of the main predicate on the type
typeMap ltypes lfamilies
  = M.fromList $
    fmap (\ ltype -> (unLocated ltype , typeIxs ltype lfamilies)) ltypes

isChallengeSupported
  :: [Located CCCChallenge] -> (a -> [Int]) -> Located a -> Bool
isChallengeSupported lcccchals findTypeIxs lt
  = any (`elem` (findTypeIxs . unLocated) lt) . 
    fmap (\ (Located _ (CCCChallenge (Located _ j))) -> j) $ 
    lcccchals

isConvertSupported
  :: [Located CCCConversion] -> (a -> [Int]) -> Located (a , a) -> Bool
isConvertSupported lcccconverts findTypeIxs lpair
  = let
      (iis , ois)
        = bimap findTypeIxs findTypeIxs . unLocated $ lpair
    in
    any (\ (oj , ij) -> elem ij iis && elem oj ois) .
    fmap (\ (Located _ (CCCConversion (Located _ oj) (Located _ ij))) -> (oj , ij)) $ 
    lcccconverts

findPlugins
  :: [Located (CCCPlugin T.Text)] -> T.Text -> [Versioned T.Text]
findPlugins lcccplugins name
  = sortOn _versionedVer . 
    filter (\ Versioned{..} -> _versionedName == name) . 
    fmap (\ (Located _ (CCCPlugin (Located _ pl))) -> pl) $
    lcccplugins

findSupportedRings
  :: UniqMap (Located Integer) -> (MainRing Integer -> [Int]) -> PredData -> [Located (MainRing Integer)]
findSupportedRings umap findTypeIxs
  = filter (not . null . findTypeIxs . unLocated) . 
    fmap (fmap (fmap (unLocated . flip findUM umap))) . 
    collectTypes lookupUnknown

findSupportedChallenges
  :: UniqMap (Located Integer) -> [Located CCCChallenge] -> (MainRing Integer -> [Int]) -> PredData -> [Located (MainRing Integer)]
findSupportedChallenges umap lcccchals findTypeIxs
  = filter (isChallengeSupported lcccchals findTypeIxs) . 
    fmap (fmap (fmap (unLocated . flip findUM umap))) . 
    collectChallenges lookupUnknown

findSupportedConverts
  :: UniqMap (Located Integer) -> [Located CCCConversion] -> (MainRing Integer -> [Int]) -> PredData -> [Located (MainRing Integer , MainRing Integer)]
findSupportedConverts umap lcccconverts findTypeIxs preddata
  = let
      find2
        = fmap (unLocated . flip findUM umap)
    in
    filter (isConvertSupported lcccconverts findTypeIxs) $
    (fmap (fmap (bimap find2 find2)) . collectConverts lookupUnknown $ preddata) ++
    (fmap (fmap (bimap id find2)) . collectConvertFromKnowns lookupUnknown $ preddata) ++
    (fmap (fmap (bimap find2 id)) . collectConvertToKnowns lookupUnknown $ preddata)

sequenceMap
  :: (Uniquable k)
  => [k] -> UniqMap [a] -> [UniqMap a]
sequenceMap names listMap
  = fmap (fromListUM . zip names) $
    sequence $
    fmap (flip findUM listMap) $
    names

forCollectingMaps
  :: [a] -> (a -> b) -> IM.IntMap b
forCollectingMaps xs
  = IM.fromList . zip [0 .. ] . (<&>) xs

-- Plugins that are allowed to be missing even in presence of the corresponding type predicate.
-- A warning is issued rather than an error if missing.
liberalPlugins
  :: [T.Text]
liberalPlugins
  = ["iter"]

checkConfiguration
  :: (MonadIO m)
  => TypedProgram -> CCC T.Text -> m TestData
checkConfiguration prog ccc
  | isNothing mMainType
    = throw $ "Function main not found"
  | not . null . filter ((/= KindNat) . tyVarKind) $ _typeSchemeQuantifiers mainType
    = throw $ "Type arguments of kind other than Natural not allowed in main"
  | not . null $ unknownBitwiseRings
    = throw $ "The argument of the bitwise type constructor is not allowed to have an unknown value in main"
  | not . null $ otherpreds
    = throwAtLocations "Predicate not allowed in main" $ otherpreds
  | not . null $ typeChecksBlackList
    = throwAtLocations "Type not supported by CCC" $ typeChecksBlackList
  | not . null $ challengeChecksBlackList
    = throwAtLocations "Challenge not supported by CCC" $ challengeChecksBlackList
  | not . null $ convertChecksBlackList
    = throwAtLocations "Conversion not supported by CCC" $ convertChecksBlackList
  | not . null $ pluginChecksBlackList
    = throwAtLocations "Plugin not supported by CCC" $ pluginChecksBlackList
  | null $ evaluations
    = throw $ "Cannot find a mapping of type parameters of main to default values satisfying ccc restrictions"
  | otherwise
    = do
        {-
        liftIO . putStrLn . render $ "knownNaturals:" <+> pretty knownNaturals
        liftIO . putStrLn . render $ "unknownNaturals:" <+> pretty unknownNaturals
        liftIO . putStrLn . render $ "assumed fields:" <+> pretty (_fields . _assumed $ mainpred)
        liftIO . putStrLn . render $ "tested fields:" <+> pretty (_fields . _tested $ mainpred)
        liftIO . putStrLn . render $ "fieldNames:" <+> pretty fieldNames
        liftIO . putStrLn . render $ "assumed challenges:" <+> pretty (_challenges . _assumed $ mainpred)
        liftIO . putStrLn . render $ "tested challenges:" <+> pretty (_challenges . _tested $ mainpred)
        liftIO . putStrLn . render $ "challengeNames:" <+> pretty challengeNames
        liftIO . putStrLn . render $ "assumed conversions:" <+> pretty (_converts . _assumed $ mainpred)
        liftIO . putStrLn . render $ "tested conversions:" <+> pretty (_converts . _tested $ mainpred)
        liftIO . putStrLn . render $ "convertNames:" <+> pretty convertNames
        liftIO . putStrLn . render $ "defaults:" <+> pretty defaults
        liftIO . putStrLn . render $ "evaluation:" $$ vcat (fmap (\ name -> pretty name <> "=" <> pretty (unLocated (findUM name evaluation))) quantifierNames)
        -}
        when (not (null pluginChecksGrayList)) $ printAtLocations "Plugin not supported by CCC" $ pluginChecksGrayList
        return $ TestData
          { _supportedRings      = sortWithoutRep $
                                   fmap unLocated (knownAssumedRings ++ knownTestedRings) ++ 
                                   fmap unLocated (unknownAssumedRings ++ unknownTestedRings)
          , _supportedChallenges = sortWithoutRep $ 
                                   fmap unLocated (knownAssumedChallenges ++ knownTestedChallenges) ++ 
                                   fmap unLocated (unknownAssumedChallenges ++ unknownTestedChallenges)
          , _supportedConverts   = sortWithoutRep $ 
                                   fmap unLocated (knownAssumedConverts ++ knownTestedConverts) ++ 
                                   fmap unLocated (unknownAssumedConverts ++ unknownTestedConverts)
          , _supportedPlugins    = pluginWhiteList
          , _mainTypeParamsEval  = evaluation
          }
  where
    mMainType@ ~(Just mainType)
      = findFunType mainFName $ prog
    (mainpred, otherpreds)
      = classifyPredicates $ _typeSchemePredicates mainType
    knownRings
      = collectAll lookupKnown mainpred
    knownAssumedRings
      = collectTypes lookupKnown (_assumed mainpred)
    knownAssumedChallenges
      = collectChallenges lookupKnown (_assumed mainpred)
    knownAssumedConverts
      = collectConverts lookupKnown (_assumed mainpred)
    (unknownPlainRings , unknownBitwiseRings)
      = partition ((Plain ==) . _rcon) (fmap unLocated (collectAll lookupUnknown mainpred))
    unknownNaturals = fmap _arg unknownPlainRings
    defaults
      = _tDefaultFields . _tProgDefaults $ prog
    typeFamilyMap
      = typeMap (if null unknownNaturals then knownRings else knownRings ++ fmap (fmap (MR Plain)) defaults) $ _cccTypes ccc
    findTypeIxs
      = unLocated . (M.!) typeFamilyMap
    typeChecksBlackList
      = filter (null . findTypeIxs . unLocated) $ knownAssumedRings
    challengeChecksBlackList
      = filter (not . isChallengeSupported (_cccChallenges ccc) findTypeIxs) $ knownAssumedChallenges
    convertChecksBlackList
      = filter (not . isConvertSupported (_cccConversions ccc) findTypeIxs) $ knownAssumedConverts
    (pluginChecksGrayList , pluginChecksBlackList)
      = partition (flip elem liberalPlugins . unLocated) $ 
        filter (null . findPlugins (_cccPlugins ccc) . unLocated) $ 
        _plugins (_assumed mainpred)
    knownTestedRings
      = filter (not . null . findTypeIxs . unLocated) . collectTypes lookupKnown $ _tested mainpred
    knownTestedChallenges
      = filter (isChallengeSupported (_cccChallenges ccc) findTypeIxs) . collectChallenges lookupKnown $ _tested mainpred
    knownTestedConverts
      = filter (isConvertSupported (_cccConversions ccc) findTypeIxs) . collectConverts lookupKnown $ _tested mainpred
    pluginWhiteList
      = fmap (findPlugins (_cccPlugins ccc) . unLocated) $ _plugins (_assumed mainpred) ++ _plugins (_tested mainpred)
    quantifierNames
      = fmap varName $ _typeSchemeQuantifiers mainType
    (evaluations , assumedQuintuple , testedTriple)
      = buildMaps quantifierNames mainpred ccc defaults findTypeIxs
    (fieldNames , challengeNames , convertNames , convertFromKnownNames , convertToKnownNames)
      = assumedQuintuple
    (supportedRingMap , supportedChallengeMap , supportedConvertMap)
      = testedTriple
    countSupportedPred (_umap , i)
      = length ((IM.!) supportedRingMap i) + length ((IM.!) supportedChallengeMap i) + length ((IM.!) supportedConvertMap i)
    (evaluation , bestIx)
      = last $ sortOn countSupportedPred $ zip evaluations [0 ..]
    find2
      = fmap (unLocated . flip findUM evaluation)
    (unknownAssumedRings , unknownAssumedChallenges , unknownAssumedConverts)
      = ( fieldNames <&> fmap find2
        , challengeNames <&> fmap find2
        , (convertNames <&> fmap (bimap find2 find2)) ++ (convertFromKnownNames <&> fmap (bimap id find2)) ++ (convertToKnownNames <&> fmap (bimap find2 id))
        )
    (unknownTestedRings , unknownTestedChallenges , unknownTestedConverts)
      = ((IM.!) supportedRingMap bestIx , (IM.!) supportedChallengeMap bestIx , (IM.!) supportedConvertMap bestIx)

buildMaps
  :: [Name] -> MainPred -> CCC T.Text -> [Located Integer] -> (MainRing Integer -> [Int]) -> 
     ( [UniqMap (Located Integer)] 
     , ([Located (MainRing Name)] , [Located (MainRing Name)] , [Located (MainRing Name , MainRing Name)] , [Located (MainRing Integer , MainRing Name)] , [Located (MainRing Name , MainRing Integer)]) 
     , (IM.IntMap [Located (MainRing Integer)] , IM.IntMap [Located (MainRing Integer)] , IM.IntMap [Located (MainRing Integer , MainRing Integer)])
     )
buildMaps names mainpred ccc defaults findTypeIxs
  = let
      typeNames
        = collectTypes lookupUnknown $ _assumed mainpred
      challengeNames
        = collectChallenges lookupUnknown $ _assumed mainpred
      convertNames
        = collectConverts lookupUnknown $ _assumed mainpred
      convertFromKnownNames
        = collectConvertFromKnowns lookupUnknown $ _assumed mainpred
      convertToKnownNames
        = collectConvertToKnowns lookupUnknown $ _assumed mainpred
      filterConvert mkPair
        = filter (isConvertSupported (_cccConversions ccc) findTypeIxs . noLoc . mkPair . MR Plain . unLocated)
      listMap
        = -- filtering conversions from known to unknown
          flip (foldr (\ (i , o) -> adjustUM (filterConvert (i ,)) (_arg o))) (fmap unLocated convertFromKnownNames) $ 
          
          -- filtering conversions from unknown to known
          flip (foldr (\ (i , o) -> adjustUM (filterConvert (, o)) (_arg i))) (fmap unLocated convertToKnownNames) $
          
          -- filtering challenges
          flip (foldr (adjustUM (filter (isChallengeSupported (_cccChallenges ccc) (findTypeIxs . MR Plain))) . _arg)) (fmap unLocated challengeNames) $
          
          -- filtering fields
          flip (foldr (adjustUM (filter (not . null . findTypeIxs . MR Plain . unLocated)) . _arg)) (fmap unLocated typeNames) $ 
          
          -- all defaults
          fromListUM (fmap (, defaults) names)
      mapList
        = sequenceMap names listMap
      evaluations
        = filter (\ umap -> all (isConvertSupported (_cccConversions ccc) (findTypeIxs . fmap (unLocated . flip findUM umap))) convertNames) $
          mapList
      supportedRingMap
        = forCollectingMaps evaluations $ \ umap -> findSupportedRings umap findTypeIxs $ _tested mainpred
      supportedChallengeMap
        = forCollectingMaps evaluations $ \ umap -> findSupportedChallenges umap (_cccChallenges ccc) findTypeIxs $ _tested mainpred
      supportedConvertMap
        = forCollectingMaps evaluations $ \ umap -> findSupportedConverts umap (_cccConversions ccc) findTypeIxs $ _tested mainpred
    in
    ( evaluations
    , (typeNames , challengeNames , convertNames , convertFromKnownNames , convertToKnownNames)
    , (supportedRingMap , supportedChallengeMap , supportedConvertMap)
    )

