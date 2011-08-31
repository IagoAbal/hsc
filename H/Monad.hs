{-# LANGUAGE GeneralizedNewtypeDeriving,
             StandaloneDeriving,
             FlexibleInstances,
             MultiParamTypeClasses,
             NamedFieldPuns,
             TypeSynonymInstances
             #-}
module H.Monad where

import H.Message
import H.SrcLoc
import H.SrcContext
import H.Pretty

import Unique

import Control.Monad.Error
import Control.Monad.RWS.Strict

import Data.IORef

newtype H env log st a = H { unH :: RWST (Henv env) log st (ErrorT Message IO) a }
  deriving (Functor, Monad, MonadIO)

runH :: H env log st a -> SrcContext -> UniqSupply -> env -> st -> IO (Either Message (a,st,log),UniqSupply)
runH m (SrcContext loc descr isprop) us env st0 = do
  us_ref <- newIORef us
  let henv0 = Henv [(loc,descr)] isprop us_ref env
  res <- runErrorT (runRWST (unH m) henv0 st0)
  us' <- readIORef us_ref
  return (res,us')

data Henv env
  = Henv {
      henv_ctxts  :: [(SrcLoc,CtxtDescr)]
    , henv_isprop :: !Bool
    , henv_us     :: !(IORef UniqSupply)
    , henv_env    :: env
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

instance Monoid log => MonadContext (H env log st) where
  getContext = H $ asks mkSrcContext
    where mkSrcContext (Henv ctxts isprop _ _)
            = SrcContext loc descr isprop
            where loc = fst $ head ctxts
                  descr = vcat $ map snd ctxts
  inContext descr m = do
    ctxt:_ <- H $ asks henv_ctxts
    let ctxt' = (fst ctxt,descr)
    H $ local (\h@Henv{henv_ctxts} -> h{henv_ctxts = ctxt':henv_ctxts}) $ unH m
  inContextAt loc descr = H . local (\h@Henv{henv_ctxts} -> h{henv_ctxts = ctxt':henv_ctxts}) . unH
    where ctxt' = (loc, descr <+> text "at" <+> pretty loc)
  inPropContext = H . local (\h -> h{henv_isprop = True}) . unH
  popContext = H . local (\h@Henv{henv_ctxts} -> h{henv_ctxts = tail henv_ctxts}) . unH


instance Monoid log => MonadError Message (H env log st) where
  throwError msg = do
    ctxt <- getContext
    H $ lift $ throwError $ contextualizeMessage ctxt msg
  m `catchError` h
    = H $ m' `catchError` h'
    where m'   = unH m
          h' e = unH $ h e 
