{-# LANGUAGE GeneralizedNewtypeDeriving,
             StandaloneDeriving,
             FlexibleInstances,
             MultiParamTypeClasses,
             NamedFieldPuns
             #-}
module H.Monad where

import H.Message ( Message )
import qualified H.Message as Msg
import H.SrcContext
import H.Pretty

import Unique

-- import Control.Failure
import Control.Monad.Error
import Control.Monad.RWS.Strict

import Data.IORef

newtype H env log st a = H { unH :: RWST (Henv env) log st (ErrorT Message IO) a }
  deriving (Functor, Monad, MonadIO)

runH :: H env log st a -> SrcContext -> UniqSupply -> env -> st -> IO (Either Message (a,st,log))
runH m ctx us env st0 = do us_ref <- newIORef us
                           let henv0 = Henv [ctx] us_ref env
                           runErrorT (runRWST (unH m) henv0 st0)

data Henv env
  = Henv {
      henv_ctx  :: [SrcContext]
    , henv_us   :: !(IORef UniqSupply)
    , henv_env  :: env
    }

deriving instance Monoid log => MonadWriter log (H env log st)
deriving instance Monoid log => MonadState st (H env log st)

instance Monoid log => MonadReader env (H env log st) where
  ask = H (asks henv_env)
  local f = H . local (\h@Henv{henv_env} -> h{henv_env = f henv_env}) . unH

instance Monoid log => MonadUnique (H env log st) where
  getUniq = H $ do us_ref <- asks henv_us
                   us <- liftIO $ readIORef us_ref
                   let uniq = next us
                   let us' = rest us
                   liftIO $ writeIORef us_ref us'
                   return uniq

instance Monoid log => MonadSrcContext (H env log st) where
  getContextStack = H (asks henv_ctx)
  inContext descr m = do ctx:_ <- getContextStack
                         let ctx' = SrcContext (ctxLoc ctx) descr
                         H $ local (\h@Henv{henv_ctx} -> h{henv_ctx = ctx':henv_ctx}) $ unH m
  inContextAt loc descr = H . local (\h@Henv{henv_ctx} -> h{henv_ctx = ctx':henv_ctx}) . unH
    where ctx' = SrcContext loc (descr <+> text "at" <+> pretty loc)
  popContext  = H . local (\h@Henv{henv_ctx} -> h{henv_ctx = tail henv_ctx}) . unH
  contextualize msg = do ctxs <- getContextStack
                         let loc = ctxLoc $ head ctxs
                             msgCtx = vcat [ descr | SrcContext _ descr <- ctxs ]
                         return $ Msg.atSrcLoc (Msg.inContext msg msgCtx) loc


failH :: Monoid log => Message -> H env log st a
failH msg = do msg' <- contextualize msg
               H $ lift $ throwError msg'
