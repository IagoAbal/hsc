{-# LANGUAGE CPP #-}
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

import Name
import Unique( Uniq, Uniquable(..) )

import Data.List ( mapAccumL )
import Data.Map( Map )
import qualified Data.Map as Map
import Data.Set( Set )
import qualified Data.Set as Set

#include "bug.h"



-- * One-shot substition

new_uniq :: Subst1 -> Uniq
new_uniq Subst1{substVarScope=varScope,substTyVarScope=tvScope}
  = 1 + Set.findMax scopeUniqs
  where scopeUniqs = Set.map uniqOf tvScope
                      `Set.union` Set.map uniqOf varScope

new_name :: Subst1 -> Name -> Name
new_name s n = n{nameUniq=new_uniq s}

new_tv :: Subst1 -> TyVar -> TyVar
new_tv s tv@TyV{tyVarName} = tv{tyVarName=new_name s tyVarName}

data Subst1 = Subst1 {
                substVarEnv     :: Map Var Exp
              , substTyVarEnv   :: Map TyVar   Tau
                -- | variables in scope,
                -- overapproximating the set of free variables
              , substVarScope   :: Set Var
              , substTyVarScope :: Set TyVar
              }

mkSubst1 :: [(Var,Exp)] -> [(TyVar,Tau)] -> Set Var -> Set TyVar -> Subst1
mkSubst1 var_env tyvar_env varScope tvScope
  = Subst1 (Map.fromList var_env) (Map.fromList tyvar_env) varScope tvScope


substBndrs :: Subst1 -> [Var] -> (Subst1,[Var])
substBndrs = mapAccumL substBndr

substBndr :: Subst1 -> Var -> (Subst1,Var)
substBndr s@Subst1{substVarEnv,substVarScope} var@V{varName,varType} =
  if var `Set.member` substVarScope
        -- @var@ may capture some variable 
     then let varName' = new_name s varName
              var'   = mkVar varName' varType'
              env'   = Map.insert var (Var var') substVarEnv
              scope' = Set.insert var' substVarScope
            in (s{substVarEnv=env',substVarScope=scope'},var')
        -- @var@ will not capture any variable
     else let var'   = mkVar varName varType'
              env'   = Map.delete var substVarEnv   -- restrict domain
              env''  = Map.insert var (Var var') env'
              scope' = Set.insert var substVarScope -- update scope
            in (s{substVarEnv=env'',substVarScope=scope'},var')
  where varType' = substType s varType

substTyBndrs :: Subst1 -> [TyVar] -> (Subst1,[TyVar])
substTyBndrs = mapAccumL substTyBndr

substTyBndr :: Subst1 -> TyVar -> (Subst1,TyVar)
substTyBndr s@Subst1{substTyVarEnv,substTyVarScope} tv =
  if tv `Set.member` substTyVarScope
        -- @tv@ may capture some variable 
     then let tv'    = new_tv s tv
              env'   = Map.insert tv (VarTy tv') substTyVarEnv
              scope' = Set.insert tv' substTyVarScope
            in (s{substTyVarEnv = env', substTyVarScope = scope'},tv')
        -- @tv@ will not capture any variable
     else let env'   = Map.delete tv substTyVarEnv   -- restrict domain
              scope' = Set.insert tv substTyVarScope -- update scope
            in (s{substTyVarEnv = env', substTyVarScope = scope'},tv)


substDecls :: Subst1 -> [Decl] -> (Subst1,[Decl])
substDecls = mapAccumL substDecl

substDecl :: Subst1 -> Decl -> (Subst1,Decl)
substDecl s (TypeDecl tynm tyargs ty) = (s,TypeDecl tynm tyargs ty')
  where ty' = substType s ty
substDecl s (DataDecl tynm tyargs cons) = (s,DataDecl tynm tyargs cons')
  where cons' = substConDecls s cons
substDecl s (ValDecl bind)
  = (s',ValDecl bind')
  where (s',bind') = substBind s bind
substDecl s (GoalDecl gname gtype typs prop)
  = (s,GoalDecl gname gtype typs prop')
  where prop' = substExp s prop


substConDecls :: Subst1 -> [ConDecl] -> [ConDecl]
substConDecls s = map (substConDecl s)

substConDecl :: Subst1 -> ConDecl -> ConDecl
substConDecl s (ConDecl con args) = (ConDecl con . snd) $ substDoms s args

substBinds :: Subst1 -> [Bind] -> (Subst1,[Bind])
substBinds = mapAccumL substBind

substBind :: Subst1 -> Bind -> (Subst1,Bind)
substBind s (FunBind NonRec fun typs args rhs)
  = (s',FunBind NonRec fun' typs' args' rhs')
  where (s_rhs',typs') = substTyBndrs s typs
        (s_rhs,args') = substBndrs s_rhs' args
        rhs' = substRhs s_rhs rhs  -- non-recursive bindings
        (s',fun') = substBndr s fun
substBind s (FunBind Rec fun typs args rhs)
  = (s',FunBind Rec fun' typs' args' rhs')
  where (s',fun') = substBndr s fun
        (s_rhs',typs') = substTyBndrs s' typs
        (s_rhs,args') = substBndrs s_rhs' args
        rhs' = substRhs s_rhs rhs  -- recursive bindings
  

substExps :: Subst1 -> [Exp] -> [Exp]
substExps s = map (substExp s)

substMaybeExp :: Subst1 -> Maybe Exp -> Maybe Exp
substMaybeExp _s Nothing  = Nothing
substMaybeExp  s (Just e) = Just $ substExp s e

substExp :: Subst1 -> Exp -> Exp
substExp Subst1{substVarEnv} e@(Var x)
  = maybe e id $ Map.lookup x substVarEnv
substExp _s par@(Par _) = par
substExp _s con@(Con _) = con
substExp _s lit@(Lit _) = lit
substExp s (PrefixApp op e) = PrefixApp (substOpExp s op) (substExp s e)
substExp s (InfixApp e1 op e2)
  = InfixApp (substExp s e1) (substOpExp s op) (substExp s e2)
substExp s (App f n) = App (substExp s f) (substExp s n)
substExp s (TyApp e tys) = TyApp (substExp s e) (substTypes s tys)
substExp s (Lam xs rhs) = Lam xs' $ substRhs s' rhs
  where (s',xs') = substBndrs s xs
substExp s (TyLam tvs e) = TyLam tvs' $ substExp s' e
  where (s',tvs') = substTyBndrs s tvs
substExp s (Let binds body) = Let binds' $ substExp s' body
  where (s',binds') = substBinds s binds
substExp s (Ite ty g t e)
  = Ite (substType s ty) (substExp s g) (substExp s t) (substExp s e)
substExp s (If ty grhss)
  = If (substType s ty) (substGuardedRhss s grhss)
substExp s (Case ty e alts)
  = Case (substType s ty) (substExp s e) (substAlts s alts)
substExp s (Tuple ty es) = Tuple (substType s ty) (substExps s es)
substExp s (List ty es) = List (substType s ty) (substExps s es)
substExp s (Paren e) = Paren $ substExp s e
substExp s (EnumFromTo e1 en) = EnumFromTo (substExp s e1) (substExp s en)
substExp s (EnumFromThenTo e1 e2 en)
  = EnumFromThenTo (substExp s e1) (substExp s e2) (substExp s en)
substExp s (Coerc e ty) = Coerc (substExp s e) (substType s ty)
substExp s (LetP pat e prop) = LetP pat' e' prop'
  where e' = substExp s e
        (s',pat') = substPat s pat
        prop' = substExp s' prop
substExp s (QP q xs body) = QP q xs' $ substExp s' body
  where (s',xs') = substBndrs s xs

substOpExp :: Subst1 -> OpExp -> OpExp
substOpExp s (OpExp tys op) = OpExp (substTypes s tys) op

substRhs :: Subst1 -> Rhs -> Rhs
substRhs s (Rhs ty expr) = Rhs (substType s ty) (substExp s expr)

substGuardedRhss :: Subst1 -> GuardedRhss -> GuardedRhss
substGuardedRhss s (GuardedRhss pgrhss elserhs)
  = GuardedRhss (map (substGuardedRhs s) pgrhss) (substElse s elserhs)

substGuardedRhs :: Subst1 -> GuardedRhs -> GuardedRhs
substGuardedRhs s (GuardedRhs g e) = GuardedRhs (substExp s g) (substExp s e)

substElse :: Subst1 -> Maybe Exp -> Maybe Exp
substElse = substMaybeExp

substPats :: Subst1 -> [Pat] -> (Subst1,[Pat])
substPats = mapAccumL substPat

substPat :: Subst1 -> Pat -> (Subst1,Pat)
substPat s (VarPat var) = (s',VarPat var')
  where (s',var') = substBndr s var
substPat s p@(LitPat _) = (s,p)
substPat s (ConPat tys con ps) = (s',ConPat tys' con ps')
  where (s',ps') = substPats s ps
        tys' = substTypes s tys
substPat s (TuplePat ty ps) = (s',TuplePat ty' ps')
  where ty' = substType s ty
        (s',ps') = substPats s ps
substPat s (ParenPat p) = (s',ParenPat p')
  where (s',p') = substPat s p


substAlts :: Subst1 -> [Alt] -> [Alt]
substAlts s = map (substAlt s)

substAlt :: Subst1 -> Alt -> Alt
substAlt s (Alt pat rhs) = Alt pat' $ substRhs s' rhs
  where (s',pat') = substPat s pat

substTypes :: Subst1 -> [Type c] -> [Type c]
substTypes s = map (substType s)

substType :: Subst1 -> Type c -> Type c
substType Subst1{substTyVarEnv} ty@(VarTy tyvar)
  = case Map.lookup tyvar substTyVarEnv of
        Just ty' -> tau2type ty'
        Nothing  -> ty
substType s (ConTy tc args) = ConTy tc $ substTypes s args
substType s (PredTy pat ty mb_prop)
  = PredTy pat' ty' $ substMaybeExp s' mb_prop
  where ty' = substType s ty
        (s',pat') = substPat s pat
substType s (FunTy dom rang) = FunTy dom' $ substType s' rang
  where (s',dom') = substDom s dom
substType s (ListTy ty) = ListTy $ substType s ty
substType s (TupleTy ds) = (TupleTy . snd) $ substDoms s ds
substType s (ForallTy tvs ty) =  ForallTy tvs' $ substType s' ty
  where (s',tvs') = substTyBndrs s tvs

substDoms :: Subst1 -> [Dom] -> (Subst1,[Dom])
substDoms = mapAccumL substDom

substDom :: Subst1 -> Dom -> (Subst1,Dom)
substDom s (Dom Nothing ty Nothing) = (s,Dom Nothing ty' Nothing)
  where ty' = substType s ty
substDom s (Dom (Just pat) ty mb_prop) = (s',Dom (Just pat') ty' mb_prop')
  where ty' = substType s ty
        (s',pat') = substPat s pat
        mb_prop' = substMaybeExp s' mb_prop
substDom _s _other = impossible
