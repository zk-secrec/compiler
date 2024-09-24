{-# LANGUAGE OverloadedStrings #-}
module YamlGen 
  ( 
    externToDocFun
  , functionToDocFun
  , yamlGenBuiltin
  , yamlGenModule
  , DescrMap
  ) where


import Yaml hiding (Pretty(..))

import Basic.Location
import Basic.Name
import Basic.Var
import Parser.Effect
import Parser.Syntax
import Support.Pretty
import Typing.Builtin
import Typing.TcM
import Typing.Typing

import Prelude hiding (lookup)
import Data.List (sortOn)
import Data.Map
import Data.Maybe
import Data.Text hiding (reverse, zipWith, head)


type DescrMap
  = Map Text String

data Modifier
  = Extern
  | Sieve


instance Show Modifier where
  
  show Extern
    = "extern"
  show Sieve
    = "sieve"
  

data DocFun = DocFun
  { _dFunName :: Id
  , _dFunArgs :: [SimpleFuncParam Id]
  , _dFunEff  :: Maybe (Located (PolymorphicTypeWithEffect Var))
  , _dFunMod  :: Maybe Modifier
  }

functionToDocFun
  :: TypedTopFunction -> DocFun
functionToDocFun fun
  = DocFun
    { _dFunName = _tFunName fun
    , _dFunArgs = _tFunArgs fun
    , _dFunEff  = _tFunEff fun
    , _dFunMod  = case _tFunIsSieve fun of { IsSieveFn -> Just Sieve; _ -> Nothing}
    }

externToDocFun
  :: TypedTopExtern -> DocFun
externToDocFun ext
  = DocFun
    { _dFunName = _tExtName ext
    , _dFunArgs = _tExtArgs ext
    , _dFunEff  = _tExtEff ext
    , _dFunMod  = Just Extern
    }


escapeIfNeeded
  :: Char -> String
escapeIfNeeded c
  | needsEscape c
    = ['\\', c]
  | otherwise
    = [c]
  where
    needsEscape c
      = elem c ("\\`*_{}[]<>()#+-.!|" :: String)

renderText
  :: (Pretty a)
  => a -> Text
renderText
  = pack . render . pretty

nameKindVar
  :: Var -> Text
nameKindVar var
  = let
      name
        = renderText var
    in
    case tyVarKind var of
      KindDomain
        -> cons '@' name
      KindStage
        -> cons '$' name
      kind
        -> name `append` " : " `append` renderText kind

nameTypeArg
  :: Int -> Type Var -> YamlObj
nameTypeArg i ty
  = YamlMapObj . fromList $
    [ ("modifier" , YamlStrVal "")
    , ("name" , YamlStrVal ("x" ++ show i))
    , ("type" , YamlStrVal (render (pretty ty) >>= escapeIfNeeded))
    ]

yamlGenFunArg
  :: SimpleFuncParam Id -> Type Id -> YamlObj
yamlGenFunArg (SimpleFuncParam style name) ty
  = YamlMapObj . fromList $
    [ ("modifier" , YamlStrVal (case style of { PassByValue -> ""; _ -> "ref" }))
    , ("name" , YamlStrVal (unpack (nameOccName . varName $ name) >>= escapeIfNeeded))
    , ("type" , YamlStrVal (render (pretty ty) >>= escapeIfNeeded))
    ]

yamlGenFun
  :: DescrMap -> DocFun -> YamlObj
yamlGenFun descrmap docfun
  = let
      name
        = nameOccName . varName . _dFunName $ docfun
      ty
        = idType . _dFunName $ docfun
      (argtys , resty)
        = splitFuncType (_typeSchemeType ty)
      args
        = zipWith yamlGenFunArg (_dFunArgs docfun) argtys
      descr
        = fromMaybe "" (lookup name descrmap)
    in
    YamlMapObj . fromList $
    [ ("args" , YamlArrVal (YamlLstArr (fmap YamlObjVal args)))
    , ("return" , YamlStrVal (render (pretty resty) >>= escapeIfNeeded))
    , ("constraints" , YamlArrVal (YamlLstArr (fmap (YamlStrVal . (>>= escapeIfNeeded) . render . pretty) (_typeSchemePredicates ty))))
    , ("typeArgs" , YamlArrVal (YamlLstArr (fmap (YamlStrVal . (>>= escapeIfNeeded) . unpack . nameKindVar) (_typeSchemeQuantifiers ty))))
    , ("name" , YamlStrVal (unpack name >>= escapeIfNeeded))
    , ("modifier" , YamlStrVal (maybe "" show (_dFunMod docfun)))
    , ("effect" , YamlStrVal (maybe "" (render . pretty) (_dFunEff docfun)))
    , ("description" , YamlStrVal ("> " ++ descr))
    ]

yamlGenBuiltinFun
  :: DescrMap -> (Text , BuiltinInfo , TcM (TypeScheme Var)) -> TcM YamlObj
yamlGenBuiltinFun descrmap (name , _ , mkTypeScheme)
  = do
      ty <- mkTypeScheme
      let (argtys , resty) = splitFuncType (_typeSchemeType ty)
      let descr = fromMaybe "" (lookup name descrmap)
      return $ YamlMapObj . fromList $
        [ ("args" , YamlArrVal (YamlLstArr (fmap YamlObjVal (zipWith nameTypeArg [1 .. ] argtys))))
        , ("return" , YamlStrVal (render (pretty resty) >>= escapeIfNeeded))
        , ("constraints" , YamlArrVal (YamlLstArr (fmap (YamlStrVal . (>>= escapeIfNeeded) . render . pretty) (_typeSchemePredicates ty))))
        , ("typeArgs" , YamlArrVal (YamlLstArr (fmap (YamlStrVal . (>>= escapeIfNeeded) . unpack . nameKindVar) (_typeSchemeQuantifiers ty))))
        , ("name" , YamlStrVal (unpack name >>= escapeIfNeeded))
        , ("modifier" , YamlStrVal "")
        , ("effect" , YamlStrVal "")
        , ("description" , YamlStrVal ("> " ++ descr))
        ]

yamlGenDoc
  :: String -> [YamlObj] -> YamlVal
yamlGenDoc name
  = singletonObjVal "api" .
    YamlArrVal . 
    YamlLstArr .
    (singletonObjVal "module" (YamlStrVal name) :) .
    fmap (singletonObjVal "function" . YamlObjVal)

yamlGenModule
  :: String -> DescrMap -> [DocFun] -> YamlVal
yamlGenModule name descrmap
  = yamlGenDoc name . fmap (yamlGenFun descrmap) . sortOn (nameOccName . varName . _dFunName)

yamlGenBuiltin
  :: String -> DescrMap -> TcM YamlVal
yamlGenBuiltin name descrmap
  = do
      objs <- traverse (yamlGenBuiltinFun descrmap) (sortOn (\ (fn , _ , _) -> fn) builtinTypes)
      return (yamlGenDoc name objs)

