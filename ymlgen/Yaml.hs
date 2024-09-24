{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Yaml where


import Data.Map hiding (foldr)


data YamlVal
  = YamlObjVal YamlObj
  | YamlArrVal YamlArr
  | YamlStrVal YamlStr

newtype YamlObj
  = YamlMapObj (Map String YamlVal)

newtype YamlArr
  = YamlLstArr [YamlVal]

type YamlStr
  = String


isYamlArr
  :: YamlVal -> Bool
isYamlArr (YamlArrVal _)
  = True
isYamlArr _
  = False

prompt
  :: Int -> Bool -> String
prompt ind isLstElem
  | isLstElem
    = replicate (ind - 2) ' ' ++ "- "
  | otherwise
    = replicate ind ' '

class Pretty a where

  pretty
    :: Int -> Bool -> a -> String

  prettys
    :: Int -> Bool -> a -> String -> String

  prettys ind isLstElem val cont
    = pretty ind isLstElem val ++ cont

  pretty ind isLstElem val
    = prettys ind isLstElem val ""


instance {-# OVERLAPPING #-} Pretty String where

  prettys ind isLstElem str cont
    = prompt ind isLstElem ++ shows str ('\n' : cont)


instance {-# OVERLAPPABLE #-} (Pretty a) => Pretty [a] where
  
  prettys ind isLstElem xs cont
    | isLstElem
      = prettys ind isLstElem "" mainpart
    | otherwise
      = mainpart
    where
      mainpart
        = foldr (\ x acc -> prettys (ind + 2) True x acc) cont xs
  

instance Pretty (Map String YamlVal) where
  
  prettys ind isLstElem map cont
    = foldr (\ (isLstElem , (k , v)) acc -> prompt ind isLstElem ++ k ++ ":\n" ++ prettys (if isYamlArr v then ind else ind + 2) False v acc) cont $
      zip (isLstElem : repeat False) (assocs map)
  

instance Pretty YamlObj where
  
  prettys ind isLstElem (YamlMapObj map) cont
    = prettys ind isLstElem map cont
  

instance Pretty YamlArr where
  
  prettys ind isLstElem (YamlLstArr lst) cont
    = prettys ind isLstElem lst cont
  

instance Pretty YamlVal where
  
  prettys ind isLstElem (YamlObjVal obj) cont
    = prettys ind isLstElem obj cont
  prettys ind isLstElem (YamlArrVal arr) cont
    = prettys ind isLstElem arr cont
  prettys ind isLstElem (YamlStrVal str) cont
    = prettys ind isLstElem str cont
  

singletonObjVal
  :: String -> YamlVal -> YamlVal
singletonObjVal name val
  = YamlObjVal (YamlMapObj (fromList [(name , val)]))

