{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module ConfigurationCheck (checkConfiguration, fieldIxs, TestData(..)) where


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
import CCC.Checks (checkFieldPreds)
import CCC.Syntax (Versioned(..), CCC(..), CCCType(..), CCCChallenge(..), CCCConversion(..), CCCPlugin(..))
import Support.Pretty (Pretty(..), Doc, render, (<+>), ($$), vcat)
import Support.UniqMap (UniqMap, fromListUM, findUM, adjustUM)
import Support.Unique (Uniquable)
import Typing.Type
import Typing.Typing (TypedProgram(..), TypedDefault(..), findFunType)

import CompilerException


data TestData
  = TestData
    { _supportedFields     :: [Integer] -- fields that are needed in the program and supported by CCC
    , _supportedChallenges :: [Integer] -- fields where challenges are needed in the program and supported by CCC
    , _supportedConverts   :: [(Integer , Integer)] -- field pairs between which conversions are needed in the program and supported by CCC
    , _supportedPlugins    :: [[Versioned T.Text]] -- plugins that are needed in the program and supported by CCC
                                                   -- grouped by plugin families differing by version only
                                                   -- increasingly sorted by version in each family
    , _mainTypeParamsEval  :: UniqMap (Located Integer) -- evaluation of the type parameters of the main function
    }
data MainTypeArg
  = Known Integer
  | Unknown Name
  deriving (Eq)
data PredData
  = PredData
    { _fields     :: [Located MainTypeArg]
    , _challenges :: [Located MainTypeArg]
    , _converts   :: [Located (MainTypeArg, MainTypeArg)]
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
    { _fields     = []
    , _challenges = []
    , _converts   = []
    , _plugins    = []
    }

instance Pretty MainTypeArg where
  
  pretty (Known n)
    = "Known" <+> pretty n
  pretty (Unknown x)
    = "Unknown" <+> pretty x
  

findMainTypeArg
  :: Type Var -> Maybe MainTypeArg
findMainTypeArg (TNat (Finite n))
  = Just (Known (toInteger n))
findMainTypeArg (TVar var _ _)
  = Just (Unknown (varName var))
findMainTypeArg _
  = Nothing

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
  => (MainTypeArg -> Maybe a) -> MainPred -> [Located a]
collectAll lookup mp
  = let
      find preddata
        = let
            fields = mapMaybe (traverse lookup) $ _fields preddata
            challenges = mapMaybe (traverse lookup) $ _challenges preddata
            converts = mapMaybe (traverse lookup) . fmap noLoc . uncurry (++) . unzip . fmap unLocated $ _converts preddata
          in
          fields ++ challenges ++ converts
    in
    sortWithoutRepOn unLocated $ find (_assumed mp) ++ find (_tested mp)

collectFields
  :: (MainTypeArg -> Maybe a) -> PredData -> [Located a]
collectFields lookup preddata
  = mapMaybe (traverse lookup) $ _fields preddata

collectChallenges
  :: (MainTypeArg -> Maybe a) -> PredData -> [Located a]
collectChallenges lookup preddata
  = mapMaybe (traverse lookup) $ _challenges preddata

collectConverts
  :: (MainTypeArg -> Maybe a) -> PredData -> [Located (a , a)]
collectConverts lookup preddata
  = mapMaybe (traverse (\ (x , y) -> (,) <$> lookup x <*> lookup y)) $ _converts preddata

collectConvertFromKnowns
  :: (MainTypeArg -> Maybe a) -> PredData -> [Located (Integer , a)]
collectConvertFromKnowns lookup preddata
  = mapMaybe (traverse (\ (x , y) -> (,) <$> lookupKnown x <*> lookup y)) $
    filter (isKnown . fst . unLocated) $ 
    _converts preddata

collectConvertToKnowns
  :: (MainTypeArg -> Maybe a) -> PredData -> [Located (a , Integer)]
collectConvertToKnowns lookup preddata
  = mapMaybe (traverse (\ (x , y) -> (,) <$> lookup x <*> lookupKnown y)) $
    filter (isKnown . snd . unLocated) $ 
    _converts preddata

classifyPredicates
  :: [TypePred Var] -> (MainPred, [TypePred Var])
classifyPredicates
  = let
      op pred (mainpred , otherpred)
        = case pred of
            PredField t l
              | Just mta <- findMainTypeArg t
                -> (mainpred & assumed . fields %~ (Located l mta :) , otherpred)
            PredChallenge t l
              | Just mta <- findMainTypeArg t
                -> (mainpred & assumed . challenges %~ (Located l mta :) , otherpred)
            PredConvertible t1 t2 l
              | Just mta1 <- findMainTypeArg t1, Just mta2 <- findMainTypeArg t2
                -> (mainpred & assumed . converts %~ (Located l (mta1 , mta2) :) , otherpred)
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
            PredTestField t l
              | Just mta <- findMainTypeArg t
                -> (mainpred & tested . fields %~ (Located l mta :) , otherpred)
            PredTestChallenge t l
              | Just mta <- findMainTypeArg t
                -> (mainpred & tested . challenges %~ (Located l mta :) , otherpred)
            PredTestConvertible t1 t2 l
              | Just mta1 <- findMainTypeArg t1, Just mta2 <- findMainTypeArg t2
                -> (mainpred & tested . converts %~ (Located l (mta1 , mta2) :) , otherpred)
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

fieldIxs
  :: Located Integer -> [Located (CCCType T.Text)] -> Located [Int]
fieldIxs (Located l n) lfamilies
  = Located l (findIndices (checkFieldPreds n) lfamilies)

fieldMap
  :: [Located Integer] -> [Located (CCCType T.Text)] -> M.Map Integer (Located [Int]) 
  -- the values are lists of indices of CCC types embracing the key field, along with the ZKSC file location of the main predicate on the field
fieldMap lfields lfamilies
  = M.fromList (fmap (\ lfield -> (unLocated lfield , fieldIxs lfield lfamilies)) lfields)

isChallengeSupported
  :: [Located CCCChallenge] -> (a -> [Int]) -> Located a -> Bool
isChallengeSupported lcccchals findFieldIxs ln
  = any (`elem` (findFieldIxs . unLocated) ln) . fmap (\ (Located _ (CCCChallenge (Located _ j))) -> j) $ lcccchals

isConvertSupported
  :: [Located CCCConversion] -> (a -> [Int]) -> Located (a , a) -> Bool
isConvertSupported lcccconverts findFieldIxs lpair
  = let
      (iis , ois)
        = bimap findFieldIxs findFieldIxs . unLocated $ lpair
    in
    any (\ (oj , ij) -> elem ij iis && elem oj ois) .
    fmap (\ (Located _ (CCCConversion (Located _ oj) (Located _ ij))) -> (oj , ij)) $ 
    lcccconverts

findPlugins
  :: [Located (CCCPlugin T.Text)] -> T.Text -> [Versioned T.Text]
findPlugins lcccplugins name
  = sortOn _versionedVer . filter (\ Versioned{..} -> _versionedName == name) . fmap (\ (Located _ (CCCPlugin (Located _ pl))) -> pl) $
    lcccplugins

findSupportedFields
  :: UniqMap (Located Integer) -> (Integer -> [Int]) -> PredData -> [Located Integer]
findSupportedFields umap findFieldIxs
  = filter (not . null . findFieldIxs . unLocated) . fmap (fmap (unLocated . flip findUM umap)) . collectFields lookupUnknown

findSupportedChallenges
  :: UniqMap (Located Integer) -> [Located CCCChallenge] -> (Integer -> [Int]) -> PredData -> [Located Integer]
findSupportedChallenges umap lcccchals findFieldIxs
  = filter (isChallengeSupported lcccchals findFieldIxs) . fmap (fmap (unLocated . flip findUM umap)) . collectChallenges lookupUnknown

findSupportedConverts
  :: UniqMap (Located Integer) -> [Located CCCConversion] -> (Integer -> [Int]) -> PredData -> [Located (Integer , Integer)]
findSupportedConverts umap lcccconverts findFieldIxs preddata
  = let
      find2
        = unLocated . flip findUM umap
    in
    filter (isConvertSupported lcccconverts findFieldIxs) $
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
  | not . null $ otherpreds
    = throwAtLocations "Predicate not allowed in main" $ otherpreds
  | not . null $ fieldChecksBlackList
    = throwAtLocations "Field not supported by CCC" $ fieldChecksBlackList
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
          { _supportedFields     = sortWithoutRep $
                                   fmap unLocated (knownAssumedFields ++ knownTestedFields) ++ 
                                   fmap unLocated (unknownAssumedFields ++ unknownTestedFields)
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
    knownNaturals
      = collectAll lookupKnown mainpred
    knownAssumedFields
      = collectFields lookupKnown (_assumed mainpred)
    knownAssumedChallenges
      = collectChallenges lookupKnown (_assumed mainpred)
    knownAssumedConverts
      = collectConverts lookupKnown (_assumed mainpred)
    unknownNaturals
      = collectAll lookupUnknown mainpred
    defaults
      = _tDefaultFields . _tProgDefaults $ prog
    fieldFamilyMap
      = fieldMap (if null unknownNaturals then knownNaturals else knownNaturals ++ defaults) $ _cccTypes ccc
    findFieldIxs
      = unLocated . (M.!) fieldFamilyMap
    fieldChecksBlackList
      = filter (null . findFieldIxs . unLocated) $ knownAssumedFields
    challengeChecksBlackList
      = filter (not . isChallengeSupported (_cccChallenges ccc) findFieldIxs) $ knownAssumedChallenges
    convertChecksBlackList
      = filter (not . isConvertSupported (_cccConversions ccc) findFieldIxs) $ knownAssumedConverts
    (pluginChecksGrayList , pluginChecksBlackList)
      = partition (flip elem liberalPlugins . unLocated) $ 
        filter (null . findPlugins (_cccPlugins ccc) . unLocated) $ 
        _plugins (_assumed mainpred)
    knownTestedFields
      = filter (not . null . findFieldIxs . unLocated) . collectFields lookupKnown $ _tested mainpred
    knownTestedChallenges
      = filter (isChallengeSupported (_cccChallenges ccc) findFieldIxs) . collectChallenges lookupKnown $ _tested mainpred
    knownTestedConverts
      = filter (isConvertSupported (_cccConversions ccc) findFieldIxs) . collectConverts lookupKnown $ _tested mainpred
    pluginWhiteList
      = fmap (findPlugins (_cccPlugins ccc) . unLocated) $ _plugins (_assumed mainpred) ++ _plugins (_tested mainpred)
    quantifierNames
      = fmap varName $ _typeSchemeQuantifiers mainType
    (evaluations , assumedQuintuple , testedTriple)
      = buildMaps quantifierNames mainpred ccc defaults findFieldIxs
    (fieldNames , challengeNames , convertNames , convertFromKnownNames , convertToKnownNames)
      = assumedQuintuple
    (supportedFieldMap , supportedChallengeMap , supportedConvertMap)
      = testedTriple
    countSupportedPred (_umap , i)
      = length ((IM.!) supportedFieldMap i) + length ((IM.!) supportedChallengeMap i) + length ((IM.!) supportedConvertMap i)
    (evaluation , bestIx)
      = last $ sortOn countSupportedPred $ zip evaluations [0 ..]
    find2
      = unLocated . flip findUM evaluation
    (unknownAssumedFields , unknownAssumedChallenges , unknownAssumedConverts)
      = ( fieldNames <&> fmap find2 
        , challengeNames <&> fmap find2 
        , (convertNames <&> fmap (bimap find2 find2)) ++ (convertFromKnownNames <&> fmap (bimap id find2)) ++ (convertToKnownNames <&> fmap (bimap find2 id))
        )
    (unknownTestedFields , unknownTestedChallenges , unknownTestedConverts)
      = ((IM.!) supportedFieldMap bestIx , (IM.!) supportedChallengeMap bestIx , (IM.!) supportedConvertMap bestIx)

buildMaps
  :: [Name] -> MainPred -> CCC T.Text -> [Located Integer] -> (Integer -> [Int]) -> 
     ( [UniqMap (Located Integer)] 
     , ([Located Name] , [Located Name] , [Located (Name , Name)] , [Located (Integer , Name)] , [Located (Name , Integer)]) 
     , (IM.IntMap [Located Integer] , IM.IntMap [Located Integer] , IM.IntMap [Located (Integer , Integer)])
     )
buildMaps names mainpred ccc defaults findFieldIxs
  = let
      fieldNames
        = collectFields lookupUnknown $ _assumed mainpred
      challengeNames
        = collectChallenges lookupUnknown $ _assumed mainpred
      convertNames
        = collectConverts lookupUnknown $ _assumed mainpred
      convertFromKnownNames
        = collectConvertFromKnowns lookupUnknown $ _assumed mainpred
      convertToKnownNames
        = collectConvertToKnowns lookupUnknown $ _assumed mainpred
      filterConvert mkPair
        = filter (isConvertSupported (_cccConversions ccc) findFieldIxs . noLoc . mkPair . unLocated)
      listMap
        = -- filtering conversions from known to unknown
          flip (foldr (\ (i , o) -> adjustUM (filterConvert (i ,)) o)) (fmap unLocated convertFromKnownNames) $ 
          
          -- filtering conversions from unknown to known
          flip (foldr (\ (i , o) -> adjustUM (filterConvert (, o)) i)) (fmap unLocated convertToKnownNames) $
          
          -- filtering challenges
          flip (foldr (adjustUM (filter (isChallengeSupported (_cccChallenges ccc) findFieldIxs)))) (fmap unLocated challengeNames) $
          
          -- filtering fields
          flip (foldr (adjustUM (filter (not . null . findFieldIxs . unLocated)))) (fmap unLocated fieldNames) $ 
          
          -- all defaults
          fromListUM (fmap (, defaults) names)
      mapList
        = sequenceMap names listMap
      evaluations
        = filter (\ umap -> all (isConvertSupported (_cccConversions ccc) (findFieldIxs . unLocated . flip findUM umap)) convertNames) $
          mapList
      supportedFieldMap
        = forCollectingMaps evaluations $ \ umap -> findSupportedFields umap findFieldIxs $ _tested mainpred
      supportedChallengeMap
        = forCollectingMaps evaluations $ \ umap -> findSupportedChallenges umap (_cccChallenges ccc) findFieldIxs $ _tested mainpred
      supportedConvertMap
        = forCollectingMaps evaluations $ \ umap -> findSupportedConverts umap (_cccConversions ccc) findFieldIxs $ _tested mainpred
    in
    ( evaluations
    , (fieldNames , challengeNames , convertNames , convertFromKnownNames , convertToKnownNames)
    , (supportedFieldMap , supportedChallengeMap , supportedConvertMap)
    )

