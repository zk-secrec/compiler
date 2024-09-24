{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
module Support.MonoidState where


import Control.Monad.State.Strict as State
import Control.Monad.Trans


newtype MonoidStateT s m a
  = MonoidStateT { runMonoidStateT :: StateT s m a }
  deriving (Functor, Applicative, Monad)

mapMonoidStateT
  :: (StateT s1 m1 a1 -> StateT s2 m2 a2) -> MonoidStateT s1 m1 a1 -> MonoidStateT s2 m2 a2
mapMonoidStateT f
  = MonoidStateT . f . runMonoidStateT

unliftMonoidStateT
  :: (Monoid s)
  => MonoidStateT s m a -> m (a, s)
unliftMonoidStateT m
  = runStateT (runMonoidStateT m) mempty

instance MonadTrans (MonoidStateT s) where
  
  lift
    = MonoidStateT . lift

class (Monoid s) => MonoidState s m | m -> s where

  addPiece
    :: s -> m ()
  
instance (Monad m, Monoid s) => MonoidState s (MonoidStateT s m) where
  
  addPiece w
    = do
        s <- get
        MonoidStateT $ put (s <> w)
  

