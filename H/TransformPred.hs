{-# LANGUAGE GADTs, ScopedTypeVariables, NamedFieldPuns, TypeFamilies #-}

module H.TransformPred where

import H.Syntax

import Unique

import Control.Applicative ( (<|>) )
import Control.Monad



tpType :: forall c p m. (MonadUnique m, IsTc p) => (Prop p -> Maybe (Prop p)) -> Type c p -> m (Type c p)
tpType f = go
  where apply_f mb_prop = (mb_prop >>= f) <|> mb_prop
        go :: forall c1. Type c1 p -> m (Type c1 p)
        go ty@(VarTy _)     = return ty
        go (ConTy tc tys)   = liftM (ConTy tc) $ mapM go tys
        go (PredTy pat ty mb_prop) = do
          (pat',pat_s) <- tpPat f pat
          ty' <- go ty
          mb_prop' <- subst_mbExp pat_s [] mb_prop
          return (PredTy pat' ty' (apply_f mb_prop'))
        go (FunTy dom rang) = do
          (dom',dom_s) <- tpDom f dom
          rang' <- subst_type dom_s [] rang
          rang'' <- go rang'
          return (FunTy dom' rang'')
        go (ListTy t)       = liftM ListTy (go t)
        go (TupleTy ds)     = liftM TupleTy $ tpDoms f ds
        go ty@(MetaTy _)    = return ty
        go (ForallTy tvs ty) = liftM (ForallTy tvs) $ go ty
        go _other           = undefined -- impossible

tpDoms :: (MonadUnique m, IsTc p) => (Prop p -> Maybe (Prop p)) -> [Dom p] -> m [Dom p]
tpDoms _f [] = return []
tpDoms f (d:ds) = do
  (d',d_s) <- tpDom f d
  ds_d <- subst_doms d_s [] ds
  ds' <- tpDoms f ds_d
  return (d':ds')

tpDom :: (MonadUnique m, IsTc p) => (Prop p -> Maybe (Prop p)) -> Dom p -> m (Dom p, [(Var p,Exp p)])
tpDom f (Dom Nothing ty Nothing) = do
  ty' <- tpType f ty
  return (Dom Nothing ty' Nothing,[])
tpDom f (Dom (Just pat) ty mb_prop) = do
  (pat',pat_s) <- tpPat f pat
  ty' <- tpType f ty
  mb_prop' <- subst_mbExp pat_s [] mb_prop
  return  (Dom (Just pat') ty' (apply_f mb_prop'),pat_s)
  where apply_f mb_prop1 = (mb_prop1 >>= f) <|> mb_prop1
tpDom _f _other = undefined -- impossible


tpBndr :: (MonadUnique m, IsTc p) => (Prop p -> Maybe (Prop p)) -> Var p -> m (Var p, [(Var p,Exp p)])
tpBndr f x@V{varType} = do
  varType' <- tpType f varType
  let x' = x{varType = varType'}
  return (x',[(x,Var x')])


tpPat :: (MonadUnique m, IsTc p) => (Prop p -> Maybe (Prop p)) -> Pat p -> m (Pat p, [(Var p,Exp p)])
tpPat f (VarPat b) = do
  (b',b_s) <- tpBndr f b
  return (VarPat b',b_s)
tpPat _f p@(LitPat _) = return (p,[])
tpPat f (InfixCONSPat typ p1 p2) = do
  (p1',p1_s) <- tpPat f p1
  typ' <- tpType f typ
  (p2',p2_s) <- tpPat f p2
  return (InfixCONSPat typ' p1' p2',p1_s++p2_s)
tpPat f (ConPat typs con ps) = do
  (ps',ps_ss) <- liftM unzip $ mapM (tpPat f) ps
  typs' <- mapM (tpType f) typs
  return (ConPat typs' con ps', concat ps_ss)
tpPat f (TuplePat ty ps) = do
  (ps',ps_ss) <- liftM unzip $ mapM (tpPat f) ps
  ty' <- tpType f ty
  return (TuplePat ty' ps', concat ps_ss)
tpPat f (ListPat ty ps) = do
  (ps',ps_ss) <- liftM unzip $ mapM (tpPat f) ps
  ty' <- tpType f ty
  return (ListPat ty' ps' , concat ps_ss)
tpPat f (ParenPat p) = do
  (p',p_s) <- tpPat f p
  return (ParenPat p',p_s)
tpPat f (WildPat wild_var) = do
  (wild_var',wild_var_s) <- tpBndr f wild_var
  return (VarPat wild_var',wild_var_s)
tpPat f (AsPat x p) = do
  (x',x_s) <- tpBndr f x
  (p',p_s) <- tpPat f p
  return (AsPat x' p', x_s++p_s)
-- tpPat f (SigPat p ty) = do
--   ty' <- tpType f ty
--   (p',p_s) <- tpPat f p
--   return (SigPat p' ty',p_s)
tpPat _f _other = undefined -- impossible
