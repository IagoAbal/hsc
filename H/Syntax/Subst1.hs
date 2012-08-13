
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}


-- |
-- Module      :  H.Syntax.Subst1
-- Copyright   :  (c) Iago Abal 2011-2012
-- License     :  BSD3
--
-- Maintainer  :  Iago Abal, iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- One-shot substitution
-- It allows several *independent* substitutions to be performed in parallel.

module H.Syntax.Subst1 where


import H.Syntax.AST
import H.Syntax.Expr ( mkVarId )
import H.Syntax.FV
import H.Syntax.IsTc
import {-# SOURCE #-} H.Syntax.Type ( tau2type, cloneTyVar )

import Util.Monad ( mapAccumM )

import Name
import Unique( MonadUnique )

import Control.Monad
import Data.Map( Map )
import qualified Data.Map as Map
import Data.Set( Set )
import qualified Data.Set as Set
import qualified Data.Traversable as T

#include "bug.h"



-- * One-shot substition

  
data Subst1 p = Subst1 {
                substVarEnv     :: Map (Var p) (Exp p)
              , substTyVarEnv   :: Map TyVar   (Tau p)
                -- | variables in scope,
                -- overapproximating the set of free variables
              , substVarScope   :: Set (Var p)
              , substTyVarScope :: Set TyVar
              }

mkSubst1 :: [(Var p,Exp p)] -> [(TyVar,Tau p)] -> Set (Var p) -> Set TyVar -> Subst1 p
mkSubst1 var_env tyvar_env var_scope tyvar_scope
  = Subst1 (Map.fromList var_env) (Map.fromList tyvar_env) var_scope tyvar_scope

--- better names ?
mkSubst1_FV :: forall p. (VAR p ~ Var p) => [(Var p,Exp p)] -> [(TyVar,Tau p)] -> Subst1 p
mkSubst1_FV var_env tyvar_env
  = Subst1 (Map.fromList var_env) (Map.fromList tyvar_env) var_scope tyvar_scope
  where var_scope :: Set (Var p)
        var_scope = fvExps (map snd var_env) `Set.union` fvTypes (map snd tyvar_env)
        tyvar_scope = Set.empty    -- Requires ftvExps ...

subst_exp :: (MonadUnique m, IsTc p) => [(Var p,Exp p)] -> [(TyVar,Tau p)] -> Exp p -> m (Exp p)
subst_exp var_env tyvar_env = substExp (mkSubst1_FV var_env tyvar_env)

subst_mbExp :: (MonadUnique m, IsTc p) => [(Var p,Exp p)] -> [(TyVar,Tau p)] -> Maybe (Exp p) -> m (Maybe (Exp p))
subst_mbExp var_env tyvar_env = substMaybeExp (mkSubst1_FV var_env tyvar_env)

subst_rhs :: (MonadUnique m, IsTc p) => [(Var p,Exp p)] -> [(TyVar,Tau p)] -> Rhs p -> m (Rhs p)
subst_rhs var_env tyvar_env = substRhs (mkSubst1_FV var_env tyvar_env)

subst_type :: (MonadUnique m, IsTc p) => [(Var p,Exp p)] -> [(TyVar,Tau p)] -> Type c p -> m (Type c p)
subst_type var_env tyvar_env = substType (mkSubst1_FV var_env tyvar_env)

subst_doms :: (MonadUnique m, IsTc p) => [(Var p,Exp p)] -> [(TyVar,Tau p)] -> [Dom p] -> m [Dom p]
subst_doms var_env tyvar_env = liftM fst . substDoms (mkSubst1_FV var_env tyvar_env)

subst_matches :: (MonadUnique m, IsTc p) => [(Var p,Exp p)] -> [(TyVar,Tau p)] -> [Match p] -> m [Match p]
subst_matches var_env tyvar_env = substMatches (mkSubst1_FV var_env tyvar_env)

subst_condecls :: (MonadUnique m, IsTc p) => [(Var p,Exp p)] -> [(TyVar,Tau p)] -> [ConDecl p] -> m [ConDecl p]
subst_condecls var_env tyvar_env = substConDecls (mkSubst1_FV var_env tyvar_env)


substBndrs :: (MonadUnique m, IsTc p) => Subst1 p -> [Var p] -> m ([Var p],Subst1 p)
substBndrs = mapAccumM substBndr

substBndr :: (MonadUnique m, IsTc p) => Subst1 p -> Var p -> m (Var p,Subst1 p)
substBndr s@Subst1{substVarEnv,substVarScope} var@V{varName,varType} = do
  varType' <- substType s varType
  if var `Set.member` substVarScope
        -- @var@ may capture some variable 
     then do varName' <- newNameFrom varName
             let var'   = mkVarId varName' varType'
                 env'   = Map.insert var (Var var') substVarEnv
                 scope' = Set.insert var' substVarScope
             return (var',s{substVarEnv = env', substVarScope = scope'})
        -- @var@ will not capture any variable
     else do let var'   = mkVarId varName varType'
                 env'   = Map.delete var substVarEnv   -- restrict domain
                 env''  = Map.insert var (Var var') env'
                 scope' = Set.insert var substVarScope -- update scope
             return (var',s{substVarEnv = env'', substVarScope = scope'})


substTyBndrs :: (MonadUnique m, IsTc p) => Subst1 p -> [TyVar] -> m ([TyVar],Subst1 p)
substTyBndrs = mapAccumM substTyBndr

substTyBndr :: (MonadUnique m, IsTc p) => Subst1 p -> TyVar -> m (TyVar,Subst1 p)
substTyBndr s@Subst1{substTyVarEnv,substTyVarScope} tv = do
  if tv `Set.member` substTyVarScope
        -- @tv@ may capture some variable 
     then do tv' <- cloneTyVar tv
             let env'   = Map.insert tv (VarTy tv') substTyVarEnv
                 scope' = Set.insert tv' substTyVarScope
             return (tv',s{substTyVarEnv = env', substTyVarScope = scope'})
        -- @tv@ will not capture any variable
     else do let env'   = Map.delete tv substTyVarEnv   -- restrict domain
                 scope' = Set.insert tv substTyVarScope -- update scope
             return (tv,s{substTyVarEnv = env', substTyVarScope = scope'})


substDecls :: (MonadUnique m, IsTc p) => Subst1 p -> [Decl p] -> m ([Decl p],Subst1 p)
substDecls = mapAccumM substDecl

substDecl :: (MonadUnique m, IsTc p) => Subst1 p -> Decl p -> m (Decl p,Subst1 p)
substDecl s (TypeDecl loc tynm tyargs ty) = do
  ty' <- substType s ty
  return (TypeDecl loc tynm tyargs ty',s)
substDecl s (DataDecl loc tynm tyargs cons) = do
  cons' <- substConDecls s cons
  return (DataDecl loc tynm tyargs cons',s)
substDecl s (ValDecl bind) = do
  (bind',s') <- substBind s bind
  return (ValDecl bind',s')
substDecl s (GoalDecl loc gname gtype ptctyparams prop) = do
  prop' <- substExp s prop
  return (GoalDecl loc gname gtype ptctyparams prop',s)


substConDecls :: (MonadUnique m, IsTc p) => Subst1 p -> [ConDecl p] -> m [ConDecl p]
substConDecls s = mapM (substConDecl s)

substConDecl :: (MonadUnique m, IsTc p) => Subst1 p -> ConDecl p -> m (ConDecl p)
substConDecl s (ConDecl loc con args) = liftM (ConDecl loc con . fst) $ substDoms s args
substConDecl _s _other = impossible

substBinds :: (MonadUnique m, IsTc p) => Subst1 p -> [Bind p] -> m ([Bind p],Subst1 p)
substBinds = mapAccumM substBind

substBind :: (MonadUnique m, IsTc p) => Subst1 p -> Bind p -> m (Bind p,Subst1 p)
substBind s (FunBind NonRec fun sig typs matches) = do
  sig' <- substTypeSig s sig
  (typs', s') <- substTyBndrs s typs
  matches' <- substMatches s' matches  -- non-recursive bindings
  (fun',s'') <- substBndr s' fun
  return (FunBind NonRec fun' sig' typs' matches',s'')
substBind s (FunBind Rec fun sig typs matches) = do
  sig' <- substTypeSig s sig
  (fun',s') <- substBndr s fun
  (typs', s'') <- substTyBndrs s' typs
  matches' <- substMatches s'' matches  -- recursive bindings
  return (FunBind Rec fun' sig' typs' matches',s'')
substBind s (PatBind loc pat rhs) = do
  rhs' <- substRhs s rhs
  (pat',s') <- substPat s pat
  return (PatBind loc pat' rhs',s')

substTypeSig :: (MonadUnique m, IsTc p) => Subst1 p -> TypeSig p -> m (TypeSig p)
substTypeSig _s NoTypeSig           = return NoTypeSig
substTypeSig s (TypeSig loc polyty) = liftM (TypeSig loc) $ substType s polyty

substMatches :: (MonadUnique m, IsTc p) => Subst1 p -> [Match p] -> m [Match p]
substMatches s = mapM (substMatch s)

substMatch :: (MonadUnique m, IsTc p) => Subst1 p -> Match p -> m (Match p)
substMatch s (Match loc pats rhs) = do
  (pats',s') <- substPats s pats
  liftM (Match loc pats') $ substRhs s' rhs

substExps :: (MonadUnique m, IsTc p) => Subst1 p -> [Exp p] -> m [Exp p]
substExps s = mapM (substExp s)

substMaybeExp :: (MonadUnique m, IsTc p) => Subst1 p -> Maybe (Exp p) -> m (Maybe (Exp p))
substMaybeExp _s Nothing  = return Nothing
substMaybeExp  s (Just e) = liftM Just $ substExp s e

substExp :: (MonadUnique m, IsTc p) => Subst1 p -> Exp p -> m (Exp p)
substExp Subst1{substVarEnv} e@(Var x)
  = case Map.lookup x substVarEnv of
        Just e' -> return e'   -- reunique e ?
        Nothing -> return e    -- ???
substExp Subst1{substVarEnv} e@(Par x)
  = case Map.lookup x substVarEnv of
        Just e' -> return e'   -- reunique e ?
        Nothing -> return e    -- ???
substExp _s con@(Con _) = return con     -- ? constructors are not substituted...
substExp _s op@(Op _) = return op
substExp _s lit@(Lit _) = return lit
substExp s (PrefixApp op e) = liftM2 PrefixApp (substExp s op) (substExp s e)
substExp s (InfixApp e1 op e2)
  = liftM3 InfixApp (substExp s e1) (substExp s op) (substExp s e2)
substExp s (App f n) = liftM2 App (substExp s f) (substExp s n)
substExp s (TyApp e tys) = liftM2 TyApp (substExp s e) (substTypes s tys)
substExp s (Lam loc pats rhs)
    = do (pats',s') <- substPats s pats
         liftM (Lam loc pats') $ substRhs s' rhs
substExp s (TyLam tvs e) = do
  (tvs',s') <- substTyBndrs s tvs
  TyLam tvs' `liftM` substExp s' e
substExp s (Let binds body) = do
  (binds',s') <- substBinds s binds
  liftM (Let binds') $ substExp s' body
substExp s (Ite ite_ty g t e)
  = liftM4 Ite (substType s ite_ty) (substExp s g) (substExp s t) (substExp s e)
substExp s (If if_ty grhss)
  = liftM2 If (substType s if_ty) (substGuardedRhss s grhss)
substExp s (Case casety e alts)
  = liftM3 Case (substType s casety) (substExp s e) (substAlts s alts)
substExp s (Tuple ty es) = liftM2 Tuple (substType s ty) (substExps s es)
substExp s (List ty es) = liftM2 List (substType s ty) (substExps s es)
substExp s (Paren e) = liftM Paren $ substExp s e
substExp s (LeftSection e op) = liftM2 LeftSection (substExp s e) (substExp s op)
substExp s (RightSection op e) = liftM2 RightSection (substExp s op) (substExp s e)
substExp s (EnumFromTo e1 en) = liftM2 EnumFromTo (substExp s e1) (substExp s en)
substExp s (EnumFromThenTo e1 e2 en)
  = liftM3 EnumFromThenTo (substExp s e1) (substExp s e2) (substExp s en)
substExp s (Coerc loc e polyty) = liftM2 (Coerc loc) (substExp s e) (substType s polyty)
substExp s (LetP pat e prop) = do
  e' <- substExp s e
  (pat',s') <- substPat s pat
  prop' <- substExp s' prop
  return $ LetP pat' e' prop'
substExp s (QP q qvars body) = do (qvars',s') <- substQVars s qvars
                                  liftM (QP q qvars') $ substExp s' body
substExp _s _other = impossible

substRhs :: (MonadUnique m, IsTc p) => Subst1 p -> Rhs p -> m (Rhs  p)
substRhs s (Rhs rhs_ty grhs whr)
  = do rhs_ty' <- substType s rhs_ty
       (whr',s') <- substBinds s whr
       grhs' <- substGRhs s' grhs
       return $ Rhs rhs_ty' grhs' whr'

substGRhs :: (MonadUnique m, IsTc p) => Subst1 p -> GRhs p -> m (GRhs  p)
substGRhs s (UnGuarded e)   = liftM UnGuarded $ substExp s e
substGRhs s (Guarded grhss) = liftM Guarded (substGuardedRhss s grhss)

substGuardedRhss :: (MonadUnique m, IsTc p) => Subst1 p -> GuardedRhss p -> m (GuardedRhss  p)
substGuardedRhss s (GuardedRhss pgrhss elserhs)
  = liftM2 GuardedRhss (mapM (substGuardedRhs s) pgrhss) (substElse s elserhs)
substGuardedRhss _s _other = impossible

substGuardedRhs :: (MonadUnique m, IsTc p) => Subst1 p -> GuardedRhs  p -> m (GuardedRhs  p)
substGuardedRhs s (GuardedRhs loc g e) = liftM2 (GuardedRhs loc) (substExp s g) (substExp s e)

substElse :: (MonadUnique m, IsTc p) => Subst1 p -> Else p -> m (Else p)
substElse  s (Else loc e) = liftM (Else loc) $ substExp s e
substElse _s NoElse       = return NoElse

substPats :: (MonadUnique m, IsTc p) => Subst1 p -> [Pat p] -> m ([Pat p],Subst1 p)
substPats = mapAccumM substPat

substPat :: (MonadUnique m, IsTc p) => Subst1 p -> Pat p -> m (Pat p,Subst1 p)
substPat s (VarPat var) = do
  (var',s') <- substBndr s var
  return (VarPat var',s')
substPat s p@(LitPat _) = return (p,s)
substPat s (InfixCONSPat typ p1 p2)
  = do ([p1',p2'],s') <- substPats s [p1,p2]
       typ' <- substType s typ
       return (InfixCONSPat typ' p1' p2',s')
substPat s (ConPat typs con ps) = do
  (ps',s') <- substPats s ps
  typs' <- substTypes s typs
  return (ConPat typs' con ps',s')
substPat s (TuplePat ty ps) = do
  (ps',s') <- substPats s ps
  ty' <- substType s ty
  return (TuplePat ty' ps',s')
substPat s (ListPat ty ps) = do
  (ps',s') <- substPats s ps
  ty' <- substType s ty
  return (ListPat ty' ps',s')
substPat s (ParenPat p) = do (p',s') <- substPat s p
                             return (ParenPat p',s')
substPat s (WildPat wild_var) = do
  (wild_var',s') <- substBndr s wild_var
  return (WildPat wild_var',s')
  -- See [SubstBndr.AsPat]
substPat s (AsPat v p) = do (p',s') <- substPat s p
                            (v',s'') <- substBndr s' v
                            return (AsPat v' p',s'')
substPat _s _other = impossible

{- NOTE [SubstBndr.AsPat]
Since the renamer ensures that, for 'v@pat', 'v' is fresh w.r.t. FV('pat')
the order in which we call substBndr does not matter. But semantically,
we must remember that an @-pattern is translated by shifting the 'alias'
variable to the RHS as a let-binding, so to call substBndr over 'pat'
in first place is the 'most correct' way.
-}

substQVars :: (MonadUnique m, IsTc p) => Subst1 p -> [QVar p] -> m ([QVar p],Subst1 p)
substQVars = mapAccumM substQVar

substQVar :: (MonadUnique m, IsTc p) => Subst1 p -> QVar p -> m (QVar p,Subst1 p)
substQVar s (QVar var mb_ty) = do
  (var',s') <- substBndr s var
  mb_ty' <- T.mapM (substType s) mb_ty
  return (QVar var' mb_ty',s')

substAlts :: (MonadUnique m, IsTc p) => Subst1 p -> [Alt p] -> m [Alt p]
substAlts s = mapM (substAlt s)

substAlt :: (MonadUnique m, IsTc p) => Subst1 p -> Alt p -> m (Alt p)
substAlt s (Alt loc pat rhs) = do (pat',s') <- substPat s pat
                                  liftM (Alt loc pat') $ substRhs s' rhs

substTypes :: (MonadUnique m, IsTc p) => Subst1 p -> [Type c p] -> m [Type c p]
substTypes s = mapM (substType s)

substType :: (MonadUnique m, IsTc p) => Subst1 p -> Type c p -> m (Type c p)
substType Subst1{substTyVarEnv} ty@(VarTy tyvar)
  = case Map.lookup tyvar substTyVarEnv of
        Just ty' -> return $ tau2type ty'
        Nothing  -> return ty
  -- remove
substType _s ty@(ConTyIn _) = return ty
  -- remove
substType s (AppTyIn ty1 ty2) = liftM2 AppTyIn (substType s ty1) (substType s ty2)
substType s (ConTy tc args) = liftM (ConTy tc) $ mapM (substType s) args
substType s (PredTy pat ty mbProp)
  = do ty' <- substType s ty
       (pat',s') <- substPat s pat
       liftM (PredTy pat' ty') $ substMaybeExp s' mbProp
substType s (FunTy dom rang) = do (dom',s') <- substDom s dom
                                  liftM (FunTy dom') $ substType s' rang
substType s (ListTy ty) = liftM ListTy $ substType s ty
substType s (TupleTy ds) = liftM (TupleTy . fst) $ substDoms s ds
  -- substitution is not applied inside meta-types
substType _s mty@(MetaTy _mtv) = return mty
substType s (ForallTy tvs ty) = do
  (tvs',s') <- substTyBndrs s tvs
  liftM (ForallTy tvs') $ substType s' ty
substType _s _other = impossible

substDoms :: (MonadUnique m, IsTc p) => Subst1 p -> [Dom p] -> m ([Dom p],Subst1 p)
substDoms = mapAccumM substDom

substDom :: (MonadUnique m, IsTc p) => Subst1 p -> Dom p -> m (Dom p,Subst1 p)
substDom s (Dom Nothing ty Nothing) = do
  ty' <- substType s ty
  return (Dom Nothing ty' Nothing,s)
substDom s (Dom (Just pat) ty mbprop) = do
  ty' <- substType s ty
  (pat',s') <- substPat s pat
  mbprop' <- substMaybeExp s' mbprop
  return (Dom (Just pat') ty' mbprop',s')
substDom _s _other = impossible
