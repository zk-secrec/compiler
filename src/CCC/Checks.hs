{-# LANGUAGE OverloadedStrings #-}
module CCC.Checks (checkCCCSoundness, checkFieldPreds) where


import Control.Monad
import Control.Monad.IO.Class
import Data.IntSet (IntSet, fromAscList, member)

import Basic.Location
import CCC.Syntax
import CompilerException


checkCCCTypes
  :: (MonadIO m)
  => [Located (CCCType a)] -> m ()
checkCCCTypes
  = let
      -- the first extra arguments counts the defined type families and the second one collects the field types defined previously
      go i fs (Located _ field : rest)
        = case field of
            CCCField _
              -> go (i + 1) (i : fs) rest
            extfield@ (CCCExtField _ _ _)
              | not . null $ extfieldBlacklist
                -> throwAtLocations "Reference to previously undefined base field index" $ 
                   extfieldBlacklist
              | otherwise
                -> go (i + 1) fs rest
              where
                extfieldBlacklist
                  = filter (not . (`elem` fs) . stripLocation) (_cccBaseFields extfield)
            CCCRing _
              -> go (i + 1) fs rest
            CCCPluginType _
              -> go (i + 1) fs rest -- should we check plugin names?
      go _ _  _
        = return ()
    in
    go 0 []

checkCCCChallenges
  :: (MonadIO m)
  => Int -> [Located CCCChallenge] -> m ()
checkCCCChallenges n
  = let
      go (CCCChallenge lix)
        = unless (stripLocation lix < n) $
          throwAtLocation "Reference to non-existent type family index" $ 
          location lix
    in
    mapM_ (go . stripLocation)

checkCCCConversions
  :: (MonadIO m)
  => Int -> [Located CCCConversion] -> m ()
checkCCCConversions n
  = let
      go (CCCConversion loix liix)
        = let
            conversionBlacklist
              = filter ((>= n) . stripLocation) [loix, liix]
          in
          unless (null conversionBlacklist) $
          throwAtLocations "Reference to non-existent type family index" $ 
          conversionBlacklist
    in
    mapM_ (go . stripLocation)

checkCCCSoundness
  :: (MonadIO m)
  => CCC a -> m ()
checkCCCSoundness ccc
  = do
      checkCCCTypes (_cccTypes ccc)
      let n = length (_cccTypes ccc)
      checkCCCChallenges n (_cccChallenges ccc)
      checkCCCConversions n (_cccConversions ccc)

knownMersenneExps
  :: IntSet
knownMersenneExps
  = fromAscList [2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127, 521, 607, 1279, 2203, 2281, 3217, 4253, 4423, 9689, 9941, 11213, 19937, 21701, 23209, 44497, 86243, 110503, 132049, 216091, 756839, 859433, 1257787, 1398269, 2976221, 3021377, 6972593, 13466917, 20996011, 24036583, 25964951, 30402457, 32582657, 37156667, 42643801, 43112609, 57885161]

extractExpOf2
  :: (Integral a)
  => a -> (Int , a)
extractExpOf2 n
  = let
      (q , r)
        = n `divMod` 2
      (e , p)
        = extractExpOf2 q
    in
    if r == 0
      then (e + 1 , p)
      else (0 , n)

checkFieldPred
  :: Integer -> Located CCCPred -> Bool
checkFieldPred n (Located _ cccpred)
  = case cccpred of
      CCCLT (Located _ m)
        -> n < m
      CCCGT (Located _ m)
        -> n > m
      CCCEQ (Located _ m)
        -> n == m
      CCCMersenne
        -> let
             (e , p)
               = extractExpOf2 (n + 1)
           in
           p == 1 && member e knownMersenneExps
      CCCProth -- does not check primality
        -> let
             (_ , p)
               = extractExpOf2 (n - 1)
           in
           p * p < n - 1
      CCCPow2
        -> n == 2

checkFieldPreds
  :: Integer -> Located (CCCType a) -> Bool
checkFieldPreds n (Located _ (CCCField lcccpreds))
  = all (checkFieldPred n) lcccpreds
checkFieldPreds _ _
  = False


