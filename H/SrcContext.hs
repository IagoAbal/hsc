{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module H.SrcContext where

import H.SrcLoc
import H.Pretty
import H.Message ( Message )
import qualified H.Message as Msg

import Control.Monad.Reader
import Control.Monad.Identity


type ContextDescr = Doc

data SrcContext
  = SrcContext {
      ctxLoc   :: SrcLoc
    , ctxDescr :: ContextDescr
    }


class Monad m => MonadSrcContext m where
  getContextStack :: m [SrcContext] -- ^ context stack
  inContext       :: ContextDescr -> m a -> m a
  inContextAt     :: SrcLoc -> ContextDescr -> m a -> m a
  popContext      :: m a -> m a
  contextualize   :: Message -> m Message


instance MonadSrcContext m => MonadSrcContext (ReaderT r m) where
  getContextStack = lift getContextStack
  inContext ctx m = ReaderT $ \e -> inContext ctx $ runReaderT m e
  inContextAt loc ctx m = ReaderT $ \e -> inContextAt loc ctx $ runReaderT m e
  popContext m    = ReaderT $ \e -> popContext $ runReaderT m e
  contextualize   = lift . contextualize

newtype SrcContextT m a = SrcContextT { unSrcContextT :: ReaderT [SrcContext] m a }
  deriving(Functor, Monad, MonadTrans, MonadIO)

instance Monad m => MonadSrcContext (SrcContextT m) where
  getContextStack = SrcContextT ask
  inContext descr m = do ctx:_ <- getContextStack
                         let ctx' = SrcContext (ctxLoc ctx) descr
                         SrcContextT $ local (ctx':) $ unSrcContextT m
  inContextAt loc descr = SrcContextT . local (ctx':) . unSrcContextT
    where ctx' = SrcContext loc (descr <+> text "at" <+> pretty loc)
  popContext = SrcContextT . local tail . unSrcContextT
  contextualize msg = do ctxs <- getContextStack
                         let loc = ctxLoc $ head ctxs
                             msgCtx = vcat [ descr | SrcContext _ descr <- ctxs ]
                         return $ Msg.atSrcLoc (Msg.inContext msg msgCtx) loc

runSrcContextT :: Monad m => SrcContextT m a -> SrcContext -> m a
runSrcContextT m ctx = runReaderT (unSrcContextT m) [ctx]

newtype SrcContextM a = SrcContextM { unSrcContextM :: SrcContextT Identity a }
  deriving(Functor, Monad, MonadSrcContext)

runSrcContextM :: SrcContextM a -> SrcContext -> a
runSrcContextM m ctx = runIdentity $ runSrcContextT (unSrcContextM m) ctx
