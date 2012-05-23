
{-# LANGUAGE CPP #-}

module Core.Syntax.Built where


import Core.Syntax.AST
import Core.Syntax.FreeVars
import Core.Syntax.Subst1 ( subst_type )

import Unique ( evalUnique )

import Data.Data ( Data )
import Data.Foldable ( toList )
import qualified Data.Generics.Uniplate.Data as G
import qualified Data.Set as Set

#include "bug.h"



-- * Expressions

isVar :: Exp -> Maybe Var
isVar (Var x) = Just x
isVar _other  = Nothing

val2bool :: Value -> Bool
val2bool t | t == mkTrue  = True
           | t == mkFalse = False
val2bool _other = bug "val2bool: not a boolean literal"

bool2exp :: Bool -> Exp
bool2exp True = mkTrue
bool2exp False = mkFalse

filterVars :: Exp -> [Var] -> [Var]
filterVars e xs = go [] (reverse xs) e_fv
  where e_fv = fvExp e
        go acc []     _fvs = acc
        go acc (y:ys)  fvs
          | y `Set.member` fvs
            || not (Set.null y_fv)
            = go (y:acc) ys (y_fv `Set.union` fvs)
          | otherwise          = go acc ys fvs
          where y_fv = fvBndr y

mkQP :: Quantifier -> [Var] -> Prop -> Prop
mkQP _qt [] prop = prop
mkQP  qt xs prop = QP qt xs prop

mkLet :: [Bind] -> Exp -> Exp
mkLet []    e = e
mkLet binds e = case binds' of
                    [] -> e
                    _  -> Let binds' e
  where e_fv = fvExp e
        binds' = filter_bs [] (reverse binds) e_fv
        filter_bs acc [] _fvs = acc
        filter_bs acc (b:bs) fvs
          | b_x `Set.member` fvs = filter_bs (b:acc) bs (b_fv `Set.union` fvs)
          | otherwise            = filter_bs acc bs fvs
          where b_x = bsBind b
                b_fv = fvBind b

-- ** Prop

prop2bool :: Prop -> Maybe Bool
prop2bool p | p == mkTrue  = Just True
            | p == mkFalse = Just False
            | otherwise    = Nothing

isIntLit :: Exp -> Maybe Integer
isIntLit (Lit (IntLit n)) = Just n
isIntLit _other           = Nothing

isLe :: Exp -> Maybe (Exp,Exp)
isLe (InfixApp e1 (OpExp [] (BoolOp LeB)) e2) = Just (e1,e2)
isLe (InfixApp e1 (OpExp [] (BoolOp GeB)) e2) = Just (e2,e1)
isLe _other                                   = Nothing

isOr :: Prop -> Maybe (Prop,Prop)
isOr (InfixApp e1 (OpExp [] (BoolOp OrB)) e2) = Just (e1,e2)
isOr _other                                   = Nothing

isAnd :: Prop -> Maybe (Prop,Prop)
isAnd (InfixApp e1 (OpExp [] (BoolOp AndB)) e2) = Just (e1,e2)
isAnd _other                                    = Nothing

isImp :: Prop -> Maybe (Prop,Prop)
isImp (InfixApp e1 (OpExp [] (BoolOp ImpB)) e2) = Just (e1,e2)
isImp _other                                    = Nothing

isEq :: Prop -> Maybe (Exp,Exp)
isEq (InfixApp e1 (OpExp [_] (BoolOp EqB)) e2) = Just (e1,e2)
isEq _othre                                    = Nothing

infixr .==>.

(.&&.) :: Prop -> Prop -> Prop
p .&&. q
  | p == mkTrue  = q
  | p == mkFalse = mkFalse
  | otherwise    = InfixApp p (OpExp [] andOp) q

(.==>.) :: Prop -> Prop -> Prop
p .==>. q
  | p == mkTrue  = q
  | p == mkFalse = mkTrue
  | otherwise    = InfixApp p (OpExp [] impOp) q

hypo :: Prop -> Prop -> Prop
hypo = (.==>.)

conj :: [Prop] -> Prop
conj [] = mkTrue
conj ps = foldr1 (.&&.) ps

hypos :: [Prop] -> Prop -> Prop
hypos [] p = p
hypos hs p = hypo (conj hs) p

-- * TCCs

mkTccCtxtProp :: TccPropCtxt -> Prop -> Prop
mkTccCtxtProp = foldr (\h f -> hypoProp h . f) id . toList
  where hypoProp (ForAll xs)   = mkForall xs
        hypoProp (LetIn binds) = mkLet binds
        hypoProp (Facts hs)    = hypos hs

-- * Types

typesIn :: Data t => t -> [Sigma]
typesIn t = G.universeBi t ++ map tau2sigma (G.universeBi t :: [Tau])

expandSyn :: Type c -> Type c
expandSyn (ConTy (SynTyCon _   [] rhs Nothing)   [])
  = tau2type rhs
expandSyn (ConTy (SynTyCon _ typs rhs (Just us)) args)
  = tau2type $ evalUnique (subst_type [] (zip typs args) rhs) us
expandSyn _other = bug "expandSyn: not an expandable type synonym"

isFunTy :: Tau -> Maybe (Dom,Tau)
isFunTy (FunTy d r)     = Just (d,r)
isFunTy (PredTy _ ty _) = isFunTy ty
isFunTy ty | isSynTy ty = isFunTy $ expandSyn ty
isFunTy _other          = Nothing

unFunTy :: Tau -> ([Dom],Tau)
unFunTy ty
  | Just (d,t) <- isFunTy ty
  , (ds,r) <- unFunTy t
  = (d:ds,r)
  | otherwise
  = ([],ty)

isMuTy :: Type c -> Bool
isMuTy ty | isSynTy ty = isMuTy $ expandSyn ty
isMuTy (VarTy _) = True
isMuTy (ConTy _ args) = all isMuTy args
isMuTy (PredTy _ _ _) = False
isMuTy (FunTy d r) = isMuDom d && isMuTy r
isMuTy (ListTy ty) = isMuTy ty
isMuTy (TupleTy ds) = all isMuDom ds
isMuTy (ForallTy _ ty) = isMuTy ty

isMuDom :: Dom -> Bool
isMuDom (Dom Nothing ty Nothing) = isMuTy ty
isMuDom _other                   = False
