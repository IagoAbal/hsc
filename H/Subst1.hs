{-# LANGUAGE KindSignatures,
             FlexibleInstances,
             TypeSynonymInstances,
             NamedFieldPuns,
             PatternGuards,
             GADTs,
             TypeOperators,
             TypeFamilies,
             UndecidableInstances,
             ScopedTypeVariables
             #-}

-- | One-shot substitution
-- It allows several *independent* substitutions to be performed in parallel.
-- TO DO: Use GHC-like UniqSupply and implicit parameters to avoid the monadic stuff
module H.Subst1 where

import H.Syntax
import H.Phase
import H.FreeVars

import Name
import Sorted
import Unique( MonadUnique )

import Control.Arrow ( second )
import Control.Applicative ( pure, (<$>), (<*>), (<|>) )
import Control.Monad
import Data.Map( Map )
import qualified Data.Map as Map
import Data.Set( Set )
import qualified Data.Set as Set


-- * One-shot substition

  
data Subst1 p = Subst1 {
                substVarEnv     :: Map (Var p) (Exp p)
              , substTyVarEnv   :: Map TyVar   (Type p)
                -- | variables in scope,
                -- overapproximating the set of free variables
              , substVarScope   :: Set (Var p)
              , substTyVarScope :: Set TyVar
              }

mkSubst1 :: [(Var p,Exp p)] -> [(TyVar,Type p)] -> Set (Var p) -> Set TyVar -> Subst1 p
mkSubst1 var_env tyvar_env var_scope tyvar_scope
  = Subst1 (Map.fromList var_env) (Map.fromList tyvar_env) var_scope tyvar_scope

--- better names ?
mkSubst1_FV :: forall p. (VAR p ~ Var p) => [(Var p,Exp p)] -> [(TyVar,Type p)] -> Subst1 p
mkSubst1_FV var_env tyvar_env
  = Subst1 (Map.fromList var_env) (Map.fromList tyvar_env) var_scope tyvar_scope
  where var_scope :: Set (Var p)
        var_scope = fvExps (map snd var_env) `Set.union` fvTypes (map snd tyvar_env)
        tyvar_scope = Set.empty    -- Requires ftvExps ...

subst_exp :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => [(Var p,Exp p)] -> [(TyVar,Type p)] -> Exp p -> m (Exp p)
subst_exp var_env tyvar_env = substExp (mkSubst1_FV var_env tyvar_env)

subst_mbExp :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => [(Var p,Exp p)] -> [(TyVar,Type p)] -> Maybe (Exp p) -> m (Maybe (Exp p))
subst_mbExp var_env tyvar_env = substMaybeExp (mkSubst1_FV var_env tyvar_env)

subst_type :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => [(Var p,Exp p)] -> [(TyVar,Type p)] -> Type p -> m (Type p)
subst_type var_env tyvar_env = substType (mkSubst1_FV var_env tyvar_env)

subst_doms :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => [(Var p,Exp p)] -> [(TyVar,Type p)] -> [Dom p] -> m [Dom p]
subst_doms var_env tyvar_env = liftM fst . substDoms (mkSubst1_FV var_env tyvar_env)

transformPred :: forall p m. (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => (Prop p -> Maybe (Prop p)) -> Type p -> m (Type p)
transformPred f = go
  where apply_f mb_prop = (mb_prop >>= f) <|> mb_prop
        go :: Type p -> m (Type p)
        go ty@(VarTy _)     = return ty
        go (ConTy tc tys)   = liftM (ConTy tc) $ mapM go tys
        go (PredTy pat ty mb_prop) = do
          (pat',pat_s) <- go_pat pat
          ty' <- go ty
          mb_prop' <- subst_mbExp pat_s [] mb_prop
          return (PredTy pat' ty' (apply_f mb_prop'))
        go (FunTy dom rang) = do
          (dom',dom_s) <- go_dom dom
          rang' <- subst_type dom_s [] rang
          rang'' <- go rang'
          return (FunTy dom' rang'')
        go (ListTy t)       = liftM ListTy (go t)
        go (TupleTy ds)     = liftM TupleTy $ go_doms ds
        go ty@(MetaTy _)    = return ty
        go_poly :: PolyType p -> m (PolyType p)
        go_poly (ForallTy tvs ty) = liftM (ForallTy tvs) $ go ty
        go_doms :: [Dom p] -> m [Dom p]
        go_doms [] = return []
        go_doms (d:ds) = do
          (d,d_s) <- go_dom d
          ds' <- subst_doms d_s [] ds
          ds'' <- go_doms ds
          return (d:ds'')
        go_dom :: Dom p -> m (Dom p, [(Var p,Exp p)])
        go_dom (Dom Nothing ty Nothing) = do
          ty' <- go ty
          return (Dom Nothing ty Nothing,[])
        go_dom (Dom (Just pat) ty mb_prop) = do
          (pat',pat_s) <- go_pat pat
          ty' <- go ty
          mb_prop' <- subst_mbExp pat_s [] mb_prop
          return  (Dom (Just pat') ty' (apply_f mb_prop'),pat_s)
        go_bndr :: Var p -> m (Var p, [(Var p,Exp p)])
        go_bndr x@V{varType} = do
          varType' <- go_poly varType
          let x' = x{varType = varType'}
          return (x',[(x,Var x')])
        go_pat :: Pat p -> m (Pat p, [(Var p,Exp p)])
        go_pat (VarPat b) = do
          (b',b_s) <- go_bndr b
          return (VarPat b',b_s)
        go_pat p@(LitPat _) = return (p,[])
        go_pat (InfixPat p1 bcon p2) = do
          (p1',p1_s) <- go_pat p1
          (p2',p2_s) <- go_pat p2
          return (InfixPat p1' bcon p2',p1_s++p2_s)
        go_pat (ConPat con ps) = do
          (ps',ps_ss) <- liftM unzip $ mapM go_pat ps
          return (ConPat con ps', concat ps_ss)
        go_pat (TuplePat ps) = do
          (ps',ps_ss) <- liftM unzip $ mapM go_pat ps
          return (TuplePat ps', concat ps_ss)
        go_pat (ListPat ps) = do
          (ps',ps_ss) <- liftM unzip $ mapM go_pat ps
          return (ListPat ps', concat ps_ss)
        go_pat (ParenPat p) = do
          (p',p_s) <- go_pat p
          return (ParenPat p,p_s)
        go_pat WildPat = return (WildPat,[])
        go_pat (AsPat x p) = do
          (x',x_s) <- go_bndr x
          (p',p_s) <- go_pat p
          return (AsPat x' p', x_s++p_s)
        go_pat (SigPat p ty) = do
          ty' <- go ty
          (p',p_s) <- go_pat p
          return (SigPat p' ty',p_s)


mapAccumM :: Monad m => (acc -> x -> m (y,acc)) -> acc -> [x] -> m ([y], acc)
mapAccumM _ acc []     = return ([],acc)
mapAccumM f acc (x:xs) = do (y,acc') <- f acc x
                            (ys,acc'') <- mapAccumM f acc' xs
                            return (y:ys,acc'')

substBndrs :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> [Var p] -> m ([Var p],Subst1 p)
substBndrs = mapAccumM substBndr

substBndr :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> Var p -> m (Var p,Subst1 p)
substBndr s@Subst1{substVarEnv,substVarScope} var@V{varName,varType} = do
  varType' <- substPolyType s varType
  if var `Set.member` substVarScope
        -- @var@ may capture some variable 
     then do varName' <- newNameFrom varName
             let var'   = V varName' varType'
                 env'   = Map.insert var (Var var') substVarEnv
                 scope' = Set.insert var' substVarScope
             return (var',s{substVarEnv = env', substVarScope = scope'})
        -- @var@ will not capture any variable
     else do let var'   = V varName varType'
                 env'   = Map.delete var substVarEnv   -- restrict domain
                 env''  = Map.insert var (Var var') env'
                 scope' = Set.insert var substVarScope -- update scope
             return (var,s{substVarEnv = env'', substVarScope = scope'})


substTyBndrs :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> [TyVar] -> m ([TyVar],Subst1 p)
substTyBndrs = mapAccumM substTyBndr

substTyBndr :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> TyVar -> m (TyVar,Subst1 p)
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


substDecls :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> [Decl p] -> m ([Decl p],Subst1 p)
substDecls = mapAccumM substDecl

substDecl :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> Decl p -> m (Decl p,Subst1 p)
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


substConDecls :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> [ConDecl p] -> m [ConDecl p]
substConDecls s = mapM (substConDecl s)

substConDecl :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> ConDecl p -> m (ConDecl p)
substConDecl s (ConDecl loc con args) = liftM (ConDecl loc con . fst) $ substDoms s args

substBinds :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> [Bind p] -> m ([Bind p],Subst1 p)
substBinds = mapAccumM substBind

substBind :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> Bind p -> m (Bind p,Subst1 p)
substBind s (FunBind NonRec fun sig matches) = do
  sig' <- substTypeSig s sig
  matches' <- substMatches s matches  -- non-recursive bindings
  (fun',s') <- substBndr s fun
  return (FunBind NonRec fun' sig' matches',s')
substBind s (FunBind Rec fun sig matches) = do
  sig' <- substTypeSig s sig
  (fun',s') <- substBndr s fun
  matches' <- substMatches s' matches  -- recursive bindings
  return (FunBind Rec fun' sig' matches',s')
substBind s (PatBind loc pat rhs) = do
  rhs' <- substRhs s rhs
  (pat',s') <- substPat s pat
  return (PatBind loc pat' rhs',s')

substTypeSig :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> TypeSig p -> m (TypeSig p)
substTypeSig _s NoTypeSig           = return NoTypeSig
substTypeSig s (TypeSig loc polyty) = liftM (TypeSig loc) $ substPolyType s polyty

substMatches :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> [Match p] -> m [Match p]
substMatches s = mapM (substMatch s)

substMatch :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> Match p -> m (Match p)
substMatch s (Match loc pats rhs) = do
  (pats',s') <- substPats s pats
  liftM (Match loc pats') $ substRhs s' rhs

substExps :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> [Exp p] -> m [Exp p]
substExps s = mapM (substExp s)

substMaybeExp :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> Maybe (Exp p) -> m (Maybe (Exp p))
substMaybeExp s Nothing  = return Nothing
substMaybeExp s (Just e) = liftM Just $ substExp s e

substExp :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> Exp p -> m (Exp p)
substExp s@(Subst1{substVarEnv}) e@(Var x@(V name polyty))
  = case Map.lookup x substVarEnv of
        Just e' -> return e'   -- reunique e ?
        Nothing -> return e    -- ???
substExp s con@(Con _) = return con     -- ? constructors are not substituted...
substExp s lit@(Lit _) = return lit
substExp s (PrefixApp op e) =  PrefixApp op `liftM` substExp s e
substExp s (InfixApp e1 op e2)
  = liftM2 (flip InfixApp op) (substExp s e1) (substExp s e2)
substExp s (App f n) = liftM2 App (substExp s f) (substExp s n)
substExp s (TyApp e tys) = liftM2 TyApp (substExp s e) (substTypes s tys)
substExp s (Lam loc pats body)
    = do (pats',s') <- substPats s pats
         liftM (Lam loc pats') $ substExp s' body
substExp s (TyLam tvs e) = do
  (tvs',s') <- substTyBndrs s tvs
  TyLam tvs' `liftM` substExp s' e
substExp s (Let binds body) = do
  (binds',s') <- substBinds s binds
  liftM (Let binds') $ substExp s' body
substExp s (Ite g t e) = liftM3 Ite (substExp s g) (substExp s t) (substExp s e)
substExp s (If grhss) = liftM If $ substGuardedRhss s grhss
substExp s (Case e casety alts)
  = liftM3 Case (substExp s e) (substPostTcType s casety) (substAlts s alts)
substExp s (Tuple es) = liftM Tuple $ substExps s es
substExp s (List es) = liftM List $ substExps s es
substExp s (Paren e) = liftM Paren $ substExp s e
substExp s (LeftSection e op) = liftM (flip LeftSection op) $ substExp s e
substExp s (RightSection op e) = liftM (RightSection op) $ substExp s e
substExp s (EnumFromTo e1 en) = liftM2 EnumFromTo (substExp s e1) (substExp s en)
substExp s (EnumFromThenTo e1 e2 en)
  = liftM3 EnumFromThenTo (substExp s e1) (substExp s e2) (substExp s en)
substExp s (Coerc loc e polyty) = liftM2 (Coerc loc) (substExp s e) (substPolyType s polyty)
substExp s (QP q pats body) = do (pats',s') <- substPats s pats
                                 liftM (QP q pats') $ substExp s' body


substRhs :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> Rhs p -> m (Rhs  p)
substRhs s (Rhs grhs whr)
  = do (whr',s') <- substBinds s whr
       liftM (flip Rhs whr') $ substGRhs s' grhs

substGRhs :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> GRhs p -> m (GRhs  p)
substGRhs s (UnGuarded e)   = liftM UnGuarded $ substExp s e
substGRhs s (Guarded grhss) = liftM Guarded (substGuardedRhss s grhss)

substGuardedRhss :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> GuardedRhss p -> m (GuardedRhss  p)
substGuardedRhss s (GuardedRhss pgrhss elserhs)
  = liftM2 GuardedRhss (mapM (substGuardedRhs s) pgrhss) (substElse s elserhs)

substGuardedRhs :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> GuardedRhs  p -> m (GuardedRhs  p)
substGuardedRhs s (GuardedRhs loc g e) = liftM2 (GuardedRhs loc) (substExp s g) (substExp s e)

substElse :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> Else p -> m (Else p)
substElse s (Else loc e) = liftM (Else loc) $ substExp s e
substElse s NoElse       = return NoElse

substPats :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> [Pat p] -> m ([Pat p],Subst1 p)
substPats = mapAccumM substPat

substPat :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> Pat p -> m (Pat p,Subst1 p)
substPat s (VarPat var) = do (var',s') <- substBndr s var
                             return (VarPat var',s')
substPat s p@(LitPat _) = return (p,s)
substPat s (InfixPat p1 con p2)
  = do ([p1',p2'],s') <- substPats s [p1,p2]
       return (InfixPat p1' con p2',s')
substPat s (ConPat con ps) = do (ps',s') <- substPats s ps
                                return (ConPat con ps',s')
substPat s (TuplePat ps) = do (ps',s') <- substPats s ps
                              return (TuplePat ps',s')
substPat s (ListPat ps) = do (ps',s') <- substPats s ps
                             return (ListPat ps',s')
substPat s (ParenPat p) = do (p',s') <- substPat s p
                             return (ParenPat p',s')
substPat s p@WildPat = return (p,s)
  -- See [SubstBndr.AsPat]
substPat s (AsPat v p) = do (p',s') <- substPat s p
                            (v',s'') <- substBndr s' v
                            return (AsPat v' p',s'')


{- NOTE [SubstBndr.AsPat]
Since the renamer ensures that, for 'v@pat', 'v' is fresh w.r.t. FV('pat')
the order in which we call substBndr does not matter. But semantically,
we must remember that an @-pattern is translated by shifting the 'alias'
variable to the RHS as a let-binding, so to call substBndr over 'pat'
in first place is the 'most correct' way.
-}

substAlts :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> [Alt p] -> m [Alt p]
substAlts s = mapM (substAlt s)

substAlt :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> Alt p -> m (Alt p)
substAlt s (Alt loc pat rhs) = do (pat',s') <- substPat s pat
                                  liftM (Alt loc pat') $ substRhs s' rhs

substPolyType :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> PolyType p -> m (PolyType p)
substPolyType s (ForallTy tvs ty) = do
  (tvs',s') <- substTyBndrs s tvs
  liftM (ForallTy tvs') $ substType s' ty

substTypes :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> [Type p] -> m [Type p]
substTypes s = mapM (substType s)

substType :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> Type p -> m (Type p)
substType Subst1{substTyVarEnv} ty@(VarTy tyvar)
  = case Map.lookup tyvar substTyVarEnv of
        Just ty' -> return ty'
        Nothing  -> return ty
  -- remove
substType s ty@(ConTyIn _) = return ty
  -- remove
substType s (AppTyIn ty1 ty2) = liftM2 AppTyIn (substType s ty1) (substType s ty2)
substType s (ConTy tc args) = liftM (ConTy tc) $ mapM (substType s) args
substType s (PredTy pat ty mbProp)
  = do ty' <- substType s ty
       (pat',s') <- substPat s pat
       liftM (PredTy pat' ty') $ substMaybeExp s mbProp
substType s (FunTy dom rang) = do (dom',s') <- substDom s dom
                                  liftM (FunTy dom') $ substType s' rang
substType s (TupleTy ds) = liftM (TupleTy . fst) $ substDoms s ds
  -- substitution is not applied inside meta-types
substType s mty@(MetaTy _mtv) = return mty

substDoms :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> [Dom p] -> m ([Dom p],Subst1 p)
substDoms = mapAccumM substDom

substDom :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> Dom p -> m (Dom p,Subst1 p)
substDom s (Dom Nothing ty Nothing) = do
  ty' <- substType s ty
  return (Dom Nothing ty' Nothing,s)
substDom s (Dom (Just pat) ty mbprop) = do
  ty' <- substType s ty
  (pat',s') <- substPat s pat
  mbprop' <- substMaybeExp s' mbprop
  return (Dom (Just pat') ty' mbprop',s')

substPostTcType :: (MonadUnique m, VAR p ~ Var p, TyVAR p ~ TyVar) => Subst1 p -> PostTcType p -> m (PostTcType p)
substPostTcType s NoPostTc    = return NoPostTc
substPostTcType s (PostTc ty) = liftM PostTc $ substType s ty

