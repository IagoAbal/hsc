
module Core.Syntax.Subst1.Direct where

import Core.Syntax.AST
import Core.Syntax.FreeVars
import Core.Syntax.FTV
import Core.Syntax.Subst1 ( Subst1 )
import qualified Core.Syntax.Subst1 as S1

import Data.Set ( Set )
import qualified Data.Set as Set



mkSubst1FV :: [(Var,Exp)] -> [(TyVar,Tau)] -> Subst1
mkSubst1FV var_env tv_env
  = S1.mkSubst1 var_env tv_env varScope tvScope
  where env_es = map snd var_env
        env_tys = map snd tv_env
        varScope :: Set Var
        varScope = fvExps env_es `Set.union` fvTypes env_tys
        tvScope = ftvOf env_es `Set.union` ftvOf env_tys

substExp :: [(Var,Exp)] -> [(TyVar,Tau)] -> Exp -> Exp
substExp var_env tv_env = S1.substExp (mkSubst1FV var_env tv_env)

substMaybeExp :: [(Var,Exp)] -> [(TyVar,Tau)] -> Maybe Exp -> Maybe Exp
substMaybeExp var_env tv_env = S1.substMaybeExp (mkSubst1FV var_env tv_env)

substRhs :: [(Var,Exp)] -> [(TyVar,Tau)] -> Rhs -> Rhs
substRhs var_env tv_env = S1.substRhs (mkSubst1FV var_env tv_env)

substType :: [(Var,Exp)] -> [(TyVar,Tau)] -> Type c -> Type c
substType var_env tv_env = S1.substType (mkSubst1FV var_env tv_env)

substDoms :: [(Var,Exp)] -> [(TyVar,Tau)] -> [Dom] -> [Dom]
substDoms var_env tv_env = snd . S1.substDoms (mkSubst1FV var_env tv_env)
