{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Support.StackState where


import Control.Monad.State.Strict as State


class (MonadState s m) => StackState s m | m -> s where
  
  push
    :: s -> m ()
  pop
    :: m s
  getStk
    :: m [s]
  
newtype StackStateT s m a
  = StackStateT { runStackStateT :: StateT [s] m a }
  deriving (Functor, Applicative, Monad)

mapStackStateT f
  = StackStateT . f . runStackStateT

unliftStackStateT
  :: StackStateT s m a -> [s] -> m (a , [s])
unliftStackStateT m
  = runStateT (runStackStateT m)

instance (Monad m) => MonadState s (StackStateT s m) where
  
  get
    = StackStateT $ 
      head <$> get
  
  put s
    = StackStateT $ 
      modify ((s :) . tail)
  
instance (Monad m) => StackState s (StackStateT s m) where
  
  push s
    = StackStateT $
      modify (s :)
  
  pop
    = StackStateT $ do
        ~(s : ss) <- get
        put ss
        pure s
  
  getStk
    = StackStateT $ get
  
instance MonadTrans (StackStateT s) where
  
  lift m
    = StackStateT $ 
      lift m
  
withExtra
  :: (StackState a m)
  => a -> m b -> m b
withExtra i m
  = do
      push i
      r <- m
      pop
      pure r

