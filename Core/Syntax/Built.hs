
{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}

{- Remove unconstrained terms

In

  forall x0 _x xs ,
    x0 == (::) @'a _x xs ==> 1 + length @'a xs >= 0

is equivalent to

  forall xs , 1 + length @'a xs >= 0

since x0 is an unconstrained variable. The former is likely to give
some headaches to QuickCheck while generating values satisfying the
antecedent of the implication. The latter should be easily tested by
QuickCheck and can be also tested efficiently by a SMT solver encoding
'length' as an uninterpreted function.

-}

module Core.Syntax.Built where


import Core.Syntax.AST
import Core.Syntax.FreeVars
import Core.Syntax.Subst1 ( subst_type )

import Unique ( evalUnique )

import Data.Data ( Data )
import Data.Foldable ( toList )
import qualified Data.Generics.Uniplate.Data as G
import Data.List ( tails )
import Data.Set ( Set )
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

removeUncons :: Exp -> Exp
removeUncons e = let ?uvars = Set.empty in go e
  where go :: (?uvars :: Set Var) => Exp -> Exp
        go (QP ForallQ xs prop)
          | not (null xs_u)
          = let ?uvars = Set.fromList xs_u `Set.union` ?uvars
              in mkForall xs (go prop)
          where xs_u = map fst $ filter (\(y,ys) -> isUnconsVar (prop,ys) y) $
                        zip xs (tail $ tails xs)
        go (isOr -> Just (e1,e2))
          | isUnconsExp e1 = mkTrue
          | isUnconsExp e2 = mkTrue
        go (isAnd -> Just (e1,e2))
          | isUnconsExp e1 = e2
          | isUnconsExp e2 = e1
        go (isImp -> Just (e1,e2))
          | isUnconsExp e1 = e2
          | isUnconsExp e2 = mkTrue
        go t = G.descend go t


cleanup :: Exp -> Exp
cleanup = G.transform f . removeUncons
  where f (QP _qt _xs p)
          | p == mkTrue = mkTrue
          | p == mkFalse = mkFalse
        f (QP qt xs (QP qt1 ys p))
          | qt == qt1 = cleanup $ mkQP qt (xs++ys) p
        f (QP qt xs (isImp -> Just (p,QP qt1 ys q)))
          | qt == qt1 = cleanup $ mkQP qt (xs++ys) $ p .==>. q
        f (QP qt xs p)
          | xs /= xs' = mkQP qt xs' p
          where xs' = filterVars p xs
        f (isOr -> Just (e1,e2))
          | e1 == e2      = e1
          | e1 == mkTrue  = mkTrue
          | e2 == mkTrue  = mkTrue
          | e1 == mkFalse = e2
          | e2 == mkFalse = e1
        f (isAnd -> Just (e1,e2))
          | e1 == e2 = e1
          | e1 == mkTrue  = e2
          | e2 == mkTrue  = e1
          | e1 == mkFalse = mkFalse
          | e2 == mkFalse = mkFalse
        f (isImp -> Just (e1,e2))
          | e1 == e2 = mkTrue
          | e1 == mkTrue  = e2
          | e2 == mkTrue  = mkTrue
          | e1 == mkFalse = mkTrue
          | e2 == mkFalse = mkNot e1
  -- this rule is mainly useful for QuickCheck
--         f (isImp -> Just (p,isImp -> Just (q,r)))
--           = (p .&&. q) .==>. r
        f (isEq -> Just (e1,e2))
          | e1 == e2 = mkTrue
        f t = t

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

tcc2prop :: TCC -> Prop
tcc2prop (CoercionTCC _ ctxt _ _ _ prop)
  = cleanup $ mkTccCtxtProp ctxt prop
tcc2prop (CompletenessTCC _ ctxt prop)
  = cleanup $ mkTccCtxtProp ctxt prop

mkTccCtxtProp :: TccPropCtxt -> Prop -> Prop
mkTccCtxtProp = foldr (\h f -> hypoProp h . f) id . toList
  where hypoProp (ForAll xs)   = mkForall xs
        hypoProp (LetIn binds) = mkLet binds
        hypoProp (Facts hs)    = hypos hs

-- * Unconstrained terms

isUnconsVar :: Data t => t -> Var -> Bool
isUnconsVar t x = length [ y | Var y <- G.universeBi t, y == x ] == 1
                && isMuTy (varType x)

isUnconsExp :: (?uvars :: Set Var) => Exp -> Bool
isUnconsExp (Var x) = x `Set.member` ?uvars
isUnconsExp (Con _) = False
isUnconsExp (Lit _) = False
isUnconsExp (PrefixApp _op e) = isUnconsExp e
isUnconsExp (isOr -> Just (p,q)) = isUnconsExp p || isUnconsExp q
isUnconsExp (isAnd -> Just (p,q))
  | p == mkTrue = isUnconsExp q
  | q == mkTrue = isUnconsExp p
-- isUnconsExp (isEq -> Just (isVar -> Just x,e2))
--   | isMuTy (varType x) = x `Set.member` ?uvars
-- isUnconsExp t@(isEq -> Just (e1,e2))
--   | all isMuTy $ typesIn t = isUnconsExp e1 || isUnconsExp e2
isUnconsExp (isEq -> Just (e1,e2)) = isUnconsExp e1 || isUnconsExp e2
isUnconsExp _other = False


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
