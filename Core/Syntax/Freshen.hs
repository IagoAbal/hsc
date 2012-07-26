
{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}

module Core.Syntax.Freshen where

import Core.Syntax.AST
import Core.Syntax.Pretty

import Pretty
import Unique ( MonadUnique(..) )

import Control.Monad
import Data.Map ( Map )
import qualified Data.Map as Map

#include "bug.h"


type Var2Var = Map Var Var

freshenVar :: (?varMap :: Var2Var) => Var -> Var
freshenVar x = case Map.lookup x ?varMap of
                   Just y  -> y
                   Nothing -> x

freshenBndr :: (?varMap :: Var2Var, MonadUnique m) => Var -> m Var
freshenBndr = newVarFrom

freshenBndrs :: (?varMap :: Var2Var, MonadUnique m) => [Var] -> m ([Var],Var2Var)
freshenBndrs xs = do
  xs' <- mapM newVarFrom xs
  return (xs',Map.fromList $ zip xs xs')

freshenBinds :: (?varMap :: Var2Var, MonadUnique m) => [Bind] -> m ([Bind],Var2Var)
freshenBinds [] = return ([],Map.empty)
freshenBinds (b:bs) = do
  (b',(f,f')) <- freshenBind b
  let ?varMap = Map.insert f f' ?varMap
  (bs',v2v) <- freshenBinds bs
  return (b':bs',Map.insert f f' v2v)

freshenBind :: (?varMap :: Var2Var, MonadUnique m) => Bind -> m (Bind,(Var,Var))
freshenBind (FunBind NonRec f tvs xs rhs) = do
  (xs',new_xs) <- freshenBndrs xs
  rhs' <- let ?varMap = new_xs `Map.union` ?varMap
            in freshenRhs rhs
  f' <- freshenBndr f
  return (FunBind NonRec f' tvs xs' rhs',(f,f'))
freshenBind (FunBind Rec f tvs xs rhs) = do
  (xs',new_xs) <- freshenBndrs xs
  f' <- freshenBndr f
  rhs' <- let ?varMap = Map.insert f f' $ new_xs `Map.union` ?varMap
            in freshenRhs rhs
  return (FunBind Rec f' tvs xs' rhs',(f,f'))

freshenExps :: (?varMap :: Var2Var, MonadUnique m) => [Exp] -> m [Exp]
freshenExps = mapM freshenExp

freshenMbExp :: (?varMap :: Var2Var, MonadUnique m) => Maybe Exp -> m (Maybe Exp)
freshenMbExp Nothing = return Nothing
freshenMbExp (Just e) = liftM Just $ freshenExp e

freshenExp :: (?varMap :: Var2Var, MonadUnique m) => Exp -> m Exp
freshenExp (Var x)   = return $ Var $ freshenVar x
freshenExp e@(Par _) = return e
freshenExp e@(Con _) = return e
freshenExp e@(Lit _) = return e
freshenExp (PrefixApp op e) = liftM (PrefixApp op) $ freshenExp e
freshenExp (InfixApp e1 op e2) = do
  e1' <- freshenExp e1
  e2' <- freshenExp e2
  return $ InfixApp e1' op e2'
freshenExp (App e1 e2) = liftM2 App (freshenExp e1) (freshenExp e2)
freshenExp (TyApp e tys) = liftM2 TyApp (freshenExp e) (freshenTypes tys)
freshenExp (Lam bs rhs) = do
  (bs', new) <- freshenBndrs bs
  let ?varMap = new `Map.union` ?varMap
  liftM (Lam bs') $ freshenRhs rhs
freshenExp (Let bs body) = do
  (bs',new) <- freshenBinds bs
  let ?varMap = new `Map.union` ?varMap
  liftM (Let bs') $ freshenExp body
freshenExp (TyLam tvs body) = liftM (TyLam tvs) $ freshenExp body
freshenExp (Ite ty g t e)
  = liftM4 Ite (freshenType ty) (freshenExp g) (freshenExp t) (freshenExp e)
freshenExp (If ty grhss)
  = liftM2 If (freshenType ty) (freshenGuardedRhss grhss)
freshenExp (Case ty e alts)
  = liftM3 Case (freshenType ty) (freshenExp e) (freshenAlts alts)
freshenExp (Tuple ty es) = liftM2 Tuple (freshenType ty) (freshenExps es)
freshenExp (List ty es) = liftM2 List (freshenType ty) (freshenExps es)
freshenExp (Paren e) = liftM Paren $ freshenExp e
freshenExp (EnumFromTo e1 e2)
  = liftM2 EnumFromTo (freshenExp e1) (freshenExp e2)
freshenExp (EnumFromThenTo e1 e2 e3)
  = liftM3 EnumFromThenTo (freshenExp e1) (freshenExp e2) (freshenExp e3)
freshenExp (Coerc e ty) = liftM2 Coerc (freshenExp e) (freshenType ty)
freshenExp (LetP pat e prop) = do
  e' <- freshenExp e
  (pat', new) <- freshenPat pat
  let ?varMap = new `Map.union` ?varMap
  liftM (LetP pat' e') $ freshenExp prop
freshenExp (QP qt bs body) = do
  (bs', varMap') <- freshenBndrs bs
  let ?varMap = varMap'
  liftM (QP qt bs') $ freshenExp body

freshenRhs :: (?varMap :: Var2Var, MonadUnique m) => Rhs -> m Rhs
freshenRhs (Rhs ty e) = liftM2 Rhs (freshenType ty) (freshenExp e)

freshenGuardedRhss :: (?varMap :: Var2Var, MonadUnique m) =>
                        GuardedRhss -> m GuardedRhss
freshenGuardedRhss (GuardedRhss grhss mbExp)
  = liftM2 GuardedRhss (mapM freshenGuardedRhs grhss) (freshenMbExp mbExp)

freshenGuardedRhs :: (?varMap :: Var2Var, MonadUnique m) =>
                        GuardedRhs -> m GuardedRhs
freshenGuardedRhs (GuardedRhs g e)
  = liftM2 GuardedRhs (freshenExp g) (freshenExp e)

freshenPat :: (?varMap :: Var2Var, MonadUnique m) => Pat -> m (Pat,Var2Var)
freshenPat (VarPat x) = do
  x' <- newVarFrom x
  return (VarPat x', Map.fromList [(x,x')])
freshenPat pat@(LitPat _) = return (pat,Map.empty)
freshenPat (ConPat tys con pats) = do
  tys' <- freshenTypes tys
  (pats',v2v) <- freshenPats pats
  return (ConPat tys' con pats',v2v)
freshenPat (TuplePat ty pats) = do
  ty' <- freshenType ty
  (pats',v2v) <- freshenPats pats
  return (TuplePat ty' pats',v2v)
freshenPat (ParenPat pat) = do
  (pat',v2v) <- freshenPat pat
  return (ParenPat pat',v2v)

freshenPats :: (?varMap :: Var2Var, MonadUnique m) => [Pat] -> m ([Pat],Var2Var)
freshenPats pats = do
  (pats',v2vs) <- liftM unzip $ mapM freshenPat pats
  return (pats',Map.unions v2vs)

freshenAlts :: (?varMap :: Var2Var, MonadUnique m) => [Alt] -> m [Alt]
freshenAlts = mapM freshenAlt

freshenAlt :: (?varMap :: Var2Var, MonadUnique m) => Alt -> m Alt
freshenAlt (Alt pat rhs) = do
  (pat',new) <- freshenPat pat
  let ?varMap = new `Map.union` ?varMap
  liftM (Alt pat') $ freshenRhs rhs

freshenTypes :: (?varMap :: Var2Var, MonadUnique m) => [Type c] -> m [Type c]
freshenTypes = mapM freshenType 

freshenType :: (?varMap :: Var2Var, MonadUnique m) => Type c -> m (Type c)
freshenType ty@(VarTy _) = return ty
freshenType (ConTy tc tys) = liftM (ConTy tc) $ freshenTypes tys
freshenType (PredTy pat ty mbProp) = do
  ty' <- freshenType ty
  (pat',new) <- freshenPat pat
  let ?varMap = new `Map.union` ?varMap
  liftM (PredTy pat' ty') $ freshenMbExp mbProp
freshenType (FunTy d r) = do
  (d',new) <- freshenDom d
  let ?varMap = new `Map.union` ?varMap
  liftM (FunTy d') $ freshenType r
freshenType (ListTy ty) = liftM ListTy $ freshenType ty
freshenType (TupleTy ds) = liftM TupleTy $ freshenDoms ds
freshenType (ForallTy tvs ty) = liftM (ForallTy tvs) $ freshenType ty

freshenDoms :: (?varMap :: Var2Var, MonadUnique m) => [Dom] -> m [Dom]
freshenDoms [] = return []
freshenDoms (d:ds) = do
  (d',new) <- freshenDom d
  let ?varMap = new `Map.union` ?varMap
  ds' <- freshenDoms ds
  return (d':ds')

freshenDom :: (?varMap :: Var2Var, MonadUnique m) => Dom -> m (Dom,Var2Var)
freshenDom (Dom Nothing ty Nothing) = do
  ty' <- freshenType ty
  return (Dom Nothing ty' Nothing,Map.empty)
freshenDom (Dom (Just pat) ty mbProp) = do
  ty' <- freshenType ty
  (pat',new) <- freshenPat pat
  let ?varMap = new `Map.union` ?varMap
  mbProp' <- freshenMbExp mbProp
  return (Dom (Just pat') ty' mbProp',new)
freshenDom _other = impossible
