
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}

module H.Monad where


import H.Message
import H.SrcLoc
import H.SrcContext
import Pretty

import Unique

import Control.Applicative ( Applicative(..) )
import Control.Monad.Error
import Control.Monad.RWS.Strict

import Data.IORef

#include "bug.h"



newtype H env log st a = H { unH :: RWST (Henv env) log st (ErrorT Message IO) a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFix)


runH :: H env log st a -> SrcContext -> UniqSupply -> env -> st -> IO (Either Message (a,st,log),UniqSupply)
runH m (SrcContext loc descr isprop) us env st0 = do
  us_ref <- newIORef us
  let henv0 = Henv [(loc,descr)] isprop us_ref env
  res <- runErrorT (runRWST (unH m) henv0 st0)
  us' <- readIORef us_ref
  return (res,us')

bindH :: H env' log' st' a -> env' -> st'
              -> (a -> st' -> log' -> H env log st b) -> H env log st b
bindH m env' st0' f = H $ RWST $ \henv0@Henv{henv_us} st0 -> do
  let henv0' = Henv [] False henv_us env'
  (x,s,l) <- runRWST (unH m) henv0' st0'
  runRWST (unH $ f x s l) henv0 st0

bindH_ :: H env' log' st' a -> env' -> st'
              -> (a -> H env log st b) -> H env log st b
bindH_ m env' st0' f = bindH m env' st0' (\x _ _ -> f x)
  

execPrintH :: Pretty a => H env log st a -> SrcContext -> UniqSupply -> env -> st -> IO ()
execPrintH m ctx us env st = do
  (res,_) <- runH m ctx us env st
  case res of
      Left err      -> putStrLn $ render err
      Right (x,_,_) -> putStrLn $ prettyPrint x

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
                   let (uniq,us') = next us
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
