{-# LANGUAGE FlexibleContexts #-}
module Main where

import Control.Monad
import Control.Exception
import System.Environment
import qualified Data.Text

import Support.Pretty
import Basic.Location
import Parser.Monad
-- import CCC.Syntax
import CCC.SyntaxDump
import CCC.Parser
import CCC.Checks


instance Show ParseError where
  
  show err
    = render (pretty (_parseErrorLocation err) $$ ind (_parseErrorMessage err))


instance Exception ParseError where


runParser
  :: ParseState -> Parser a -> IO a
runParser state parser =
  case unParse parser state of
    ParseOK _ x -> return x
    ParseFail err -> throwIO err

initState
  :: FilePath -> IO ParseState
initState file
  = do
      let pos = Position file 1 1
      inp <- readFile file
      return ParseState
        { _parsePosition = pos
        , _parseInput = Data.Text.pack inp
        , _parseLastLoc = mkLocation pos pos
        , _parsePrevChar = '\0'
        , _parseAlexState = [0]
        }

main
  :: IO ()
main
  = do
      args <- getArgs
      guard (length args == 1)
      state <- initState (args !! 0)
      ccc <- runParser state parse
      putStrLn "Starting parsing..."
      checkCCCSoundness ccc
      print (dumpCCC ccc)
