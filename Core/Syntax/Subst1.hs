{-# LANGUAGE KindSignatures,
             NamedFieldPuns,
             PatternGuards,
             TypeOperators
             #-}

-- | One-shot substitution
-- It allows several *independent* substitutions to be performed in parallel.
-- TODO: Use GHC-like UniqSupply and implicit parameters to avoid the monadic stuff
-- TODO: Review corner cases
module Core.Syntax.Subst1 where


import Core.Syntax.AST
import Core.Syntax.FreeVars

import Util.Monad ( mapAccumM )

import Name
import Unique( MonadUnique )

import Control.Monad
import Data.Map( Map )
import qualified Data.Map as Map
import Data.Set( Set )
import qualified Data.Set as Set


-- * One-shot substition

  
data Subst1 = Subst1 {
                substVarEnv     :: Map Var Exp
              , substTyVarEnv   :: Map TyVar   Tau
                -- | variables in scope,
                -- overapproximating the set of free variables
              , substVarScope   :: Set Var
              , substTyVarScope :: Set TyVar
              }

mkSubst1 :: [(Var,Exp)] -> [(TyVar,Tau)] -> Set Var -> Set TyVar -> Subst1
mkSubst1 var_env tyvar_env var_scope tyvar_scope
  = Subst1 (Map.fromList var_env) (Map.fromList tyvar_env) var_scope tyvar_scope

--- better names ?
mkSubst1_FV :: [(Var,Exp)] -> [(TyVar,Tau)] -> Subst1
mkSubst1_FV var_env tyvar_env
  = Subst1 (Map.fromList var_env) (Map.fromList tyvar_env) var_scope tyvar_scope
  where var_scope :: Set Var
        var_scope = fvExps (map snd var_env) `Set.union` fvTypes (map snd tyvar_env)
        tyvar_scope = Set.empty    -- Requires ftvExps ... ?

subst_exp :: MonadUnique m => [(Var,Exp)] -> [(TyVar,Tau)] -> Exp -> m Exp
subst_exp var_env tyvar_env = substExp (mkSubst1_FV var_env tyvar_env)

subst_mbExp :: MonadUnique m => [(Var,Exp)] -> [(TyVar,Tau)] -> Maybe Exp -> m (Maybe Exp)
subst_mbExp var_env tyvar_env = substMaybeExp (mkSubst1_FV var_env tyvar_env)

subst_rhs :: MonadUnique m => [(Var,Exp)] -> [(TyVar,Tau)] -> Rhs -> m Rhs
subst_rhs var_env tyvar_env = substRhs (mkSubst1_FV var_env tyvar_env)

subst_type :: MonadUnique m => [(Var,Exp)] -> [(TyVar,Tau)] -> Type c -> m (Type c)
subst_type var_env tyvar_env = substType (mkSubst1_FV var_env tyvar_env)

subst_doms :: MonadUnique m => [(Var,Exp)] -> [(TyVar,Tau)] -> [Dom] -> m [Dom]
subst_doms var_env tyvar_env = liftM fst . substDoms (mkSubst1_FV var_env tyvar_env)

subst_condecls :: MonadUnique m => [(Var,Exp)] -> [(TyVar,Tau)] -> [ConDecl] -> m [ConDecl]
subst_condecls var_env tyvar_env = substConDecls (mkSubst1_FV var_env tyvar_env)


substBndrs :: MonadUnique m => Subst1 -> [Var] -> m ([Var],Subst1)
substBndrs = mapAccumM substBndr

substBndr :: MonadUnique m => Subst1 -> Var -> m (Var,Subst1)
substBndr s@Subst1{substVarEnv,substVarScope} var@V{varName,varType} = do
  varType' <- substType s varType
  if var `Set.member` substVarScope
        -- @var@ may capture some variable 
     then do varName' <- newNameFrom varName
             let var'   = mkVar varName' varType'
                 env'   = Map.insert var (Var var') substVarEnv
                 scope' = Set.insert var' substVarScope
             return (var',s{substVarEnv = env', substVarScope = scope'})
        -- @var@ will not capture any variable
     else do let var'   = mkVar varName varType'
                 env'   = Map.delete var substVarEnv   -- restrict domain
                 env''  = Map.insert var (Var var') env'
                 scope' = Set.insert var substVarScope -- update scope
             return (var',s{substVarEnv = env'', substVarScope = scope'})


substTyBndrs :: MonadUnique m => Subst1 -> [TyVar] -> m ([TyVar],Subst1)
substTyBndrs = mapAccumM substTyBndr

substTyBndr :: MonadUnique m => Subst1 -> TyVar -> m (TyVar,Subst1)
substTyBndr s@Subst1{substTyVarEnv,substTyVarScope} tv = do
  if tv `Set.member` substTyVarScope
        -- @tv@ may capture some variable 
     then do tv' <- newTyVarFrom tv
             let env'   = Map.insert tv (VarTy tv') substTyVarEnv
                 scope' = Set.insert tv' substTyVarScope
             return (tv',s{substTyVarEnv = env', substTyVarScope = scope'})
        -- @tv@ will not capture any variable
     else do let env'   = Map.delete tv substTyVarEnv   -- restrict domain
                 scope' = Set.insert tv substTyVarScope -- update scope
             return (tv,s{substTyVarEnv = env', substTyVarScope = scope'})


substDecls :: MonadUnique m => Subst1 -> [Decl] -> m ([Decl],Subst1)
substDecls = mapAccumM substDecl

substDecl :: MonadUnique m => Subst1 -> Decl -> m (Decl,Subst1)
substDecl s (TypeDecl tynm tyargs ty) = do
  ty' <- substType s ty
  return (TypeDecl tynm tyargs ty',s)
substDecl s (DataDecl tynm tyargs cons) = do
  cons' <- substConDecls s cons
  return (DataDecl tynm tyargs cons',s)
substDecl s (ValDecl bind) = do
  (bind',s') <- substBind s bind
  return (ValDecl bind',s')
substDecl s (GoalDecl gname gtype typs prop) = do
  prop' <- substExp s prop
  return (GoalDecl gname gtype typs prop',s)


substConDecls :: MonadUnique m => Subst1 -> [ConDecl] -> m [ConDecl]
substConDecls s = mapM (substConDecl s)

substConDecl :: MonadUnique m => Subst1 -> ConDecl -> m ConDecl
substConDecl s (ConDecl con args) = liftM (ConDecl con . fst) $ substDoms s args

substBinds :: MonadUnique m => Subst1 -> [Bind] -> m ([Bind],Subst1)
substBinds = mapAccumM substBind

substBind :: MonadUnique m => Subst1 -> Bind -> m (Bind,Subst1)
substBind s (FunBind NonRec fun typs args rhs) = do
  (typs', s_rhs') <- substTyBndrs s typs
  (args',s_rhs) <- substBndrs s_rhs' args
  rhs' <- substRhs s_rhs rhs  -- non-recursive bindings
  (fun',s') <- substBndr s fun
  return (FunBind NonRec fun' typs' args' rhs',s')
substBind s (FunBind Rec fun typs args rhs) = do
  (fun',s') <- substBndr s fun
  (typs',s_rhs') <- substTyBndrs s' typs
  (args',s_rhs) <- substBndrs s_rhs' args
  rhs' <- substRhs s_rhs rhs  -- recursive bindings
  return (FunBind Rec fun' typs' args' rhs',s')
-- substBind s (PatBind pat rhs) = do
--   rhs' <- substRhs s rhs
--   (pat',s') <- substPat s pat
--   return (PatBind pat' rhs',s')
--substBind _s _other = undefined -- impossible

substExps :: MonadUnique m => Subst1 -> [Exp] -> m [Exp]
substExps s = mapM (substExp s)

substMaybeExp :: MonadUnique m => Subst1 -> Maybe Exp -> m (Maybe Exp)
substMaybeExp _s Nothing  = return Nothing
substMaybeExp  s (Just e) = liftM Just $ substExp s e

substExp :: MonadUnique m => Subst1 -> Exp -> m Exp
substExp Subst1{substVarEnv} e@(Var x)
  = case Map.lookup x substVarEnv of
        Just e' -> return e'   -- reunique e ?
        Nothing -> return e    -- ???
substExp _s con@(Con _) = return con     -- ? constructors are not substituted...
substExp _s lit@(Lit _) = return lit
-- substExp _s Undefined = return Undefined
substExp s (PrefixApp op e) = liftM2 PrefixApp (substOpExp s op) (substExp s e)
substExp s (InfixApp e1 op e2)
  = liftM3 InfixApp (substExp s e1) (substOpExp s op) (substExp s e2)
substExp s (App f n) = liftM2 App (substExp s f) (substExp s n)
substExp s (TyApp e tys) = liftM2 TyApp (substExp s e) (substTypes s tys)
substExp s (Lam vars rhs)
    = do (vars',s') <- substBndrs s vars
         liftM (Lam vars') $ substRhs s' rhs
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
substExp s (Tuple tupty es) = liftM2 Tuple (substType s tupty) (substExps s es)
substExp s (List listty es) = liftM2 List (substType s listty) (substExps s es)
substExp s (Paren e) = liftM Paren $ substExp s e
substExp s (EnumFromTo e1 en) = liftM2 EnumFromTo (substExp s e1) (substExp s en)
substExp s (EnumFromThenTo e1 e2 en)
  = liftM3 EnumFromThenTo (substExp s e1) (substExp s e2) (substExp s en)
substExp s (Coerc e ty) = liftM2 Coerc (substExp s e) (substType s ty)
substExp s (QP q vars body) = do (vars',s') <- substBndrs s vars
                                 liftM (QP q vars') $ substExp s' body

substOpExp :: MonadUnique m => Subst1 -> OpExp -> m OpExp
substOpExp s (OpExp tys op) = do
  tys' <- substTypes s tys
  return $ OpExp tys' op

substRhs :: MonadUnique m => Subst1 -> Rhs -> m Rhs
substRhs s (Rhs rhs_ty expr)
  = do rhs_ty' <- substType s rhs_ty
--        (whr',s') <- substBinds s whr
       expr' <- substExp s expr
       return $ Rhs rhs_ty' expr'

substGuardedRhss :: MonadUnique m => Subst1 -> GuardedRhss -> m GuardedRhss
substGuardedRhss s (GuardedRhss pgrhss elserhs)
  = liftM2 GuardedRhss (mapM (substGuardedRhs s) pgrhss) (substElse s elserhs)

substGuardedRhs :: MonadUnique m => Subst1 -> GuardedRhs -> m GuardedRhs
substGuardedRhs s (GuardedRhs g e) = liftM2 GuardedRhs (substExp s g) (substExp s e)

substElse :: MonadUnique m => Subst1 -> Maybe Exp -> m (Maybe Exp)
substElse = substMaybeExp

substPats :: MonadUnique m => Subst1 -> [Pat] -> m ([Pat],Subst1)
substPats = mapAccumM substPat

substPat :: MonadUnique m => Subst1 -> Pat -> m (Pat,Subst1)
substPat s (VarPat var) = do
  (var',s') <- substBndr s var
  return (VarPat var',s')
substPat s p@(LitPat _) = return (p,s)
substPat s (ConPat tys con ps) = do
  (ps',s') <- substPats s ps
  tys' <- substTypes s tys
  return (ConPat tys' con ps',s')
substPat s (TuplePat ty ps) = do
  (ps',s') <- substPats s ps
  ty' <- substType s ty
  return (TuplePat ty' ps',s')
substPat s (ParenPat p) = do (p',s') <- substPat s p
                             return (ParenPat p',s')


substAlts :: MonadUnique m => Subst1 -> [Alt] -> m [Alt]
substAlts s = mapM (substAlt s)

substAlt :: MonadUnique m => Subst1 -> Alt -> m Alt
substAlt s (Alt pat rhs) = do (pat',s') <- substPat s pat
                              liftM (Alt pat') $ substRhs s' rhs

substTypes :: MonadUnique m => Subst1 -> [Type c] -> m [Type c]
substTypes s = mapM (substType s)

substType :: MonadUnique m => Subst1 -> Type c -> m (Type c)
substType Subst1{substTyVarEnv} ty@(VarTy tyvar)
  = case Map.lookup tyvar substTyVarEnv of
        Just ty' -> return $ tau2type ty'
        Nothing  -> return ty
substType s (ConTy tc args) = liftM (ConTy tc) $ mapM (substType s) args
substType s (PredTy pat ty mbProp)
  = do ty' <- substType s ty
       (pat',s') <- substPat s pat
       liftM (PredTy pat' ty') $ substMaybeExp s' mbProp
substType s (FunTy dom rang) = do (dom',s') <- substDom s dom
                                  liftM (FunTy dom') $ substType s' rang
substType s (ListTy ty) = liftM ListTy $ substType s ty
substType s (TupleTy ds) = liftM (TupleTy . fst) $ substDoms s ds
substType s (ForallTy tvs ty) = do
  (tvs',s') <- substTyBndrs s tvs
  liftM (ForallTy tvs') $ substType s' ty

substDoms :: MonadUnique m => Subst1 -> [Dom] -> m ([Dom],Subst1)
substDoms = mapAccumM substDom

substDom :: MonadUnique m => Subst1 -> Dom -> m (Dom,Subst1)
substDom s (Dom Nothing ty Nothing) = do
  ty' <- substType s ty
  return (Dom Nothing ty' Nothing,s)
substDom s (Dom (Just pat) ty mbprop) = do
  ty' <- substType s ty
  (pat',s') <- substPat s pat
  mbprop' <- substMaybeExp s' mbprop
  return (Dom (Just pat') ty' mbprop',s')
substDom _s _other = undefined -- impossible
