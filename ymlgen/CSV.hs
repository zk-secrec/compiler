module CSV (parse) where
{- Can parse only CSV tables with two columns where every cell is a string in double quotes. -}


import YamlGen (DescrMap)

import Data.Map (fromList)
import Data.Text (Text, pack)


parseLine
  :: String -> (Text , String)
parseLine line
  = head $ do
      (name , ',' : rest) <- reads line
      (descr , _) <- reads rest
      return (pack name , descr)

parse
  :: String -> DescrMap
parse
  = fromList . fmap parseLine . lines

