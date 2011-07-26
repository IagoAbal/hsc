
{-# LANGUAGE MultiParamTypeClasses,
             GeneralizedNewtypeDeriving, 
             FlexibleContexts
             #-}

-- | Generation of unique values
module Unique
  ( Uniq
  , Uniquable(..)
  , UniqSupply, newSupply
  , MonadUnique(..)
  , UniqueT, evalUniqueT, runUniqueT
  , Unique, evalUnique, runUnique
  )
  where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State.Strict


-- * Unique values

type Uniq = Int


-- * Uniquable class
-- Types whose inhabitants are uniquely identified.

class Uniquable a where
  uniqOf :: a -> Uniq


-- * Unique supply

newtype UniqSupply = UniqSupply { next :: Uniq }

mkSupply :: Uniq -> UniqSupply
mkSupply = UniqSupply

newSupply :: UniqSupply
newSupply = mkSupply 0

pick :: UniqSupply -> (Uniq,UniqSupply)
pick (UniqSupply x) = (x,mkSupply (x+1))

rest :: UniqSupply -> UniqSupply
rest (UniqSupply x) = mkSupply (x+1)


-- * MonadUnique
-- A monad to supply unique values.

class Monad m => MonadUnique m where
  getUniq :: m Uniq


-- MonadUnique instances for some monad stacks based on lifting.

instance MonadUnique m => MonadUnique (ReaderT r m) where
  getUniq = lift getUniq


-- * UniqueT monad transformer

newtype UniqueT m a = UniqueT { unUniqueT :: StateT UniqSupply m a }
  deriving(Functor, Monad, MonadTrans, MonadIO)

evalUniqueT :: Monad m => UniqueT m a -> UniqSupply -> m a
evalUniqueT = evalStateT . unUniqueT

runUniqueT :: Monad m => UniqueT m a -> UniqSupply -> m (a, UniqSupply)
runUniqueT = runStateT . unUniqueT


instance Monad m => MonadUnique (UniqueT m) where
    getUniq = UniqueT $ do uniq <- gets next
                           modify rest
                           return uniq


-- * Unique monad

newtype Unique a = Unique { unUnique :: UniqueT Identity a }
    deriving (Functor, Monad, MonadUnique)

evalUnique :: Unique a -> UniqSupply -> a
evalUnique m s =  runIdentity $ evalUniqueT (unUnique m) s

runUnique :: Unique a -> UniqSupply -> (a,UniqSupply)
runUnique m s =  runIdentity $ runUniqueT (unUnique m) s
