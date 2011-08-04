{-# LANGUAGE TypeSynonymInstances,
             GeneralizedNewtypeDeriving
             #-}

module H.SrcContext where

import H.SrcLoc
import H.Pretty


-- * Source context

type CtxtDescr = Doc

data SrcContext
  = SrcContext {
      contextLoc    :: SrcLoc
    , contextDescr  :: CtxtDescr
    , isPropContext :: Bool
    }

class Monad m => MonadContext m where
  getContext    :: m SrcContext
  inContext     :: CtxtDescr -> m a -> m a
  inContextAt   :: SrcLoc -> CtxtDescr -> m a -> m a
  inPropContext :: m a -> m a
  popContext    :: m a -> m a
