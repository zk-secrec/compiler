module CompilerException where

import Control.Exception (throwIO)
import Control.Monad.IO.Class

import Basic.Location
import Basic.Message
import Support.Bag (singletonBag)
import Support.Pretty (Doc, pretty)


toErrMsg
  :: (HasLocation b)
  => Doc () -> [b] -> Message
toErrMsg msg bs
  = errMsg msg (fmap location bs)

toWarnMsg
  :: (HasLocation b)
  => Doc () -> [b] -> Message
toWarnMsg msg bs
  = warnMsg msg (fmap location bs)

throwAtLocations :: (MonadIO m, HasLocation b) => Doc () -> [b] -> m a
throwAtLocations msg = liftIO . throwIO . singletonBag . toErrMsg msg

throwAtLocation :: (MonadIO m, HasLocation b) => Doc () -> b -> m a
throwAtLocation msg = throwAtLocations msg . return

throw :: (MonadIO m) => String -> m a
throw msg = throwAtLocation (pretty msg) NoLocation

printAtLocations :: (MonadIO m, HasLocation b) => Doc () -> [b] -> m ()
printAtLocations msg = liftIO . print . singletonBag . toWarnMsg msg
