{-# LANGUAGE TemplateHaskell #-}

module SieveIR.Internal.Schema where

import FlatBuffers
import Language.Haskell.TH (location, loc_filename)
import System.FilePath ((</>), splitFileName)

$(do dir <- fst . splitFileName . loc_filename <$> location
     mkFlatBuffers (dir </> "sieve.fbs") defaultOptions)
