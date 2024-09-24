{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

module DocGen
  ( generateBuiltinYAML
  , generateModuleYAML
  ) where

import Control.Lens hiding ((<.>))

import Data.Aeson
import qualified Data.ByteString as BS
import qualified Data.Map as M
import Data.Maybe (catMaybes)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Yaml as Y
import System.FilePath.Posix

import Basic.Name
import Basic.Var

import Support.Pretty
import Typing.Type
import Parser.Syntax
import Basic.Location

data DocArg = DocArg
  { _argName :: Text
  , _argType :: Text
  }

instance ToJSON DocArg where
  toJSON x = toJSON $ M.fromList
    [ ("name" :: String, toJSON $ _argName x)
    , ("type", toJSON $ _argType x)
    ]

data DocEntry
  = DocFun
    { _docName        :: Text
    , _docArgs        :: [DocArg]
    , _docReturn      :: Text
    , _docTypeArgs    :: [Text]
    , _docConstraints :: [Text]
    , _docDescription :: Text
    }

instance ToJSON DocEntry where
  toJSON x@DocFun{} = toJSON . M.singleton ("function" :: String) . toJSON $ M.fromList
    [ ("name" :: String, toJSON $ _docName x)
    , ("args", toJSON $ _docArgs x)
    , ("return", toJSON $ _docReturn x)
    , ("typeArgs", toJSON $ _docTypeArgs x)
    , ("constraints", toJSON $ _docConstraints x)
    , ("description", toJSON $ _docDescription x)
    ]

newtype DocEntries = DocEntries [DocEntry]

instance ToJSON DocEntries where
  toJSON (DocEntries x) = toJSON . M.singleton ("api" :: String) $ toJSON x

isOperator :: Text -> Bool
isOperator x = T.any (`notElem` ['a'..'z']<>['A'..'Z']<>['_','-']) x ||
               x == "-"

prettyT :: Pretty a => a -> Text
prettyT x = renderStrictText (pretty x :: Doc ())

ppTyVar :: TyVar -> Text
ppTyVar x = renderStrictText (ppNameWithKind occName kind :: Doc ())
  where
    occName = pretty . nameOccName $ varName x
    kind = tyVarKind x

ppNameWithKind :: Doc ann -> Kind -> Doc ann
ppNameWithKind name = \case
  KindDomain -> "@" <> name
  KindStage -> "$" <> name
  KindUnknown -> name
  k -> name <+> ":" <+> ppKind k

ppKind :: Kind -> Doc ann
ppKind = go never_prec
  where
    never_prec = 40
    fun_prec = 50

    go _ KindDomain = "Domain"
    go _ KindStage = "Stage"
    go _ KindNat = "Nat"
    go _ KindUnqualified = "Unqualified"
    go _ KindStar = "Qualified"
    go _ KindUnknown = "Unknown"
    go _ KindEffect = "Effect"
    go p (KindFun k1 k2) = parensIf (p > fun_prec) $
      go (fun_prec + 1) k1 <+> "->" <+> go fun_prec k2

ppTyParam :: TypeParam Text -> [Text]
ppTyParam = \case
  TypeParam (Located _ t) k -> [render t k]
  TypeParamQualify (Located _ t) ms d ->
    [render t KindUnqualified] ++
    [render s KindStage | let Just s = ms] ++
    [render d KindDomain]
  where
    render t k = renderStrictText $ ppNameWithKind (pretty t) k

generateBuiltin :: (T.Text, BuiltinInfo, TypeScheme TyVar) -> Maybe DocEntry
generateBuiltin (_docName, _, res)
  | isOperator _docName = Nothing
  | otherwise = Just DocFun{..}
  where
    typeArgs = res ^.. typeSchemeQuantifiers . folded . to ppTyVar
    t = res ^. typeSchemeType . to (fmap (nameOccName.varName))
    (argTys, resTy) = splitFuncType t
    _docArgs = [DocArg "_" t | t <- map prettyT argTys]
    _docReturn = prettyT resTy
    _docTypeArgs = typeArgs
    _docConstraints = res ^.. to _typeSchemePredicates . folded . to prettyT
    _docDescription = getDescription _docName

generateFuncParam :: FuncParam Text -> DocArg
generateFuncParam (FuncParam _ (Located _ name) ty) = DocArg name (prettyT ty)

generateSignature :: Signature Text -> Maybe DocEntry
generateSignature Signature{..}
  | not _sigIsPublic = Nothing
  | otherwise = Just DocFun{..}
  where
    _docName = unLocated _sigName
    _docReturn = prettyT _sigReturnType
    _docArgs = map generateFuncParam (unLocated _sigParameters)
    _docTypeArgs = concatMap ppTyParam (unLocated _sigTypeParameters)
    _docConstraints = [prettyT c | c <- unLocated _sigConstraints]
    _docDescription = ""

generateBuiltinYAML :: [(T.Text, BuiltinInfo, TypeScheme TyVar)] -> IO ()
generateBuiltinYAML builtins =
  let entries = map generateBuiltin builtins
  in BS.writeFile "builtins.yaml" . Y.encode . DocEntries $ catMaybes entries

generateModuleYAML :: Module (LProgram T.Text) -> IO ()
generateModuleYAML (Located _ Program{..}, moduleName, _) = do
  let entries = map (generateSignature.unLocated._funSignature.unLocated) _programTopFunctions
  BS.writeFile (moduleName <.> "yaml") . Y.encode . DocEntries $ catMaybes entries

getDescription :: Text -> Text
getDescription "mod_div" = "Calculates the remainder"
getDescription "xor" = "Calculates the logical XOR of the two booleans"
getDescription _ = ""
