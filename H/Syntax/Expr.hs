
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- |
-- Module      :  H.Syntax.Expr
-- Copyright   :  (c) Iago Abal 2011-2012
-- License     :  BSD3
--
-- Maintainer  :  Iago Abal, iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--

module H.Syntax.Expr
  where


import H.Syntax.AST
import H.Syntax.IsTc
import H.Syntax.Phase
import {-# SOURCE #-} H.Syntax.Type

import Name
import Sorted
import Unique( MonadUnique(..) )

#include "bug.h"



-- * Variables

varTau :: Var p -> Tau p
varTau = type2tau . varType

mkVarId :: Name -> Sigma p -> Var p
mkVarId name sig = V name sig False

mkSkolemVar :: Name -> Sigma p -> Var p
mkSkolemVar name sig = V name sig True

-- ** Fresh variables

newVarId :: MonadUnique m => String -> Sigma p -> m (Var p)
newVarId str ty = do
  name <- newName VarNS str
  return $ V name ty False

cloneVarId :: MonadUnique m => Var p -> m (Var p)
cloneVarId (V name ty isSk) = do
  name' <- newNameFrom name
  return $ V name' ty isSk

-- ** Quantified variables

toQVar :: VAR p -> QVar p
toQVar var = QVar var Nothing


-- * Expressions

type IntExp = Exp

instance IsTc p => Sorted Lit (Type c p) where
  sortOf (IntLit _) = intTy

isElseGuard :: Exp Pr -> Bool
isElseGuard ElseGuard = True
isElseGuard _other    = False

splitApp :: Exp p -> (Exp p,[Exp p])
splitApp = go []
  where go args (App f a) = go (a:args) f
        go args f         = (f,args)

mkInt :: Integer -> Exp p
mkInt = Lit . IntLit

zero :: Exp p
zero = mkInt 0

mkApp :: Exp p -> [Exp p] -> Exp p
mkApp f args = foldl App f args

(.<.), (.<=.), (.>.), (.>=.) :: Exp p -> Exp p -> Prop p
x .<. y = InfixApp x (Op ltOp) y
x .<=. y = InfixApp x (Op leOp) y
x .>. y = InfixApp x (Op gtOp) y
x .>=. y = InfixApp x (Op geOp) y

eq, neq :: IsTc p => Tau p -> Exp p -> Exp p -> Prop p
eq ty x y = InfixApp x (TyApp (Op eqOp) [ty]) y
neq ty x y = InfixApp x (TyApp (Op neqOp) [ty]) y

(==*), (!=*) :: IsTc p => IntExp p -> IntExp p -> Prop p
x ==* y = eq intTy x y
x !=* y = neq intTy x y

(.+.), (.-.), (.*.), (./.) :: IntExp p -> IntExp p -> IntExp p
x .+. y = InfixApp x (Op addOp) y
x .-. y = InfixApp x (Op subOp) y
x .*. y = InfixApp x (Op mulOp) y
x ./. y = InfixApp x (Op divOp) y

mkLet :: [Bind p] -> Exp p -> Exp p
mkLet [] body = body
mkLet bs body = Let bs body

mkTyApp :: Ge p Tc => Exp p -> [Tau p] -> Exp p
mkTyApp expr []  = expr
mkTyApp expr tys = TyApp expr tys

mkTyLam :: (Ge p Tc, TyVAR p ~ TyVar) => [TyVar] -> Exp p -> Exp p
mkTyLam []  expr = expr
mkTyLam tvs expr = TyLam tvs expr

mkForall :: [VAR p] -> Prop p -> Prop p
mkForall [] prop = prop
mkForall xs prop = QP ForallQ (map toQVar xs) prop

-- ** Right hand side

-- isVar :: Exp p -> Maybe (VAR p)
-- isVar (Var x) = Just x
-- isVar _other  = Nothing

isVarRhs :: Rhs p -> Maybe (VAR p)
isVarRhs (Rhs _ty (UnGuarded (Var x)) []) = Just x
isVarRhs _other                           = Nothing

lamRhs :: Rhs p -> Exp p
lamRhs (Rhs _ty (UnGuarded e) []) = e
lamRhs _other                     = bug "lamRhs: not a lambda-RHS"

mkExpRhs :: IsTc p => Tau p -> Exp p -> Rhs p
mkExpRhs ty e = Rhs ty (UnGuarded e) []

mkVarRhs :: IsTc p => Var p -> Rhs p
mkVarRhs x = mkExpRhs (varTau x) (Var x)

rhs2exp :: Rhs p -> Exp p
rhs2exp (Rhs _tc_ty (UnGuarded e) binds)
  = mkLet binds e
rhs2exp (Rhs  tc_ty (Guarded grhss) binds)
  = mkLet binds $ If tc_ty grhss

grhs2exp :: IsTc p => Tau p -> GRhs p -> Exp p
grhs2exp _ty (UnGuarded e)   = e
grhs2exp  ty (Guarded grhss) = If ty grhss


-- * Data constructors

instance IsTc p => Sorted BuiltinCon (Sigma p) where
  sortOf UnitCon  = unitTy
  sortOf FalseCon = boolTy
  sortOf TrueCon  = boolTy
  sortOf NilCon   = mkForallTy [a_tv] $ ListTy a
    where a_nm = mkUsrName (mkOccName TyVarNS "a") a_uniq
          a_uniq = -11
          a_tv = TyV a_nm typeKi False
          a = VarTy a_tv
  sortOf ConsCon  = mkForallTy [a_tv] $ a --> ListTy a --> ListTy a
    where a_nm = mkUsrName (mkOccName TyVarNS "a") a_uniq
          a_uniq = -12
          a_tv = TyV a_nm typeKi False
          a = VarTy a_tv

instance IsTc p => Sorted (Con p) (Sigma p) where
  sortOf (UserCon ucon)    = sortOf ucon
  sortOf (BuiltinCon bcon) = sortOf bcon

instance IsTc p => Sorted (TcCon p) (Sigma p) where
  sortOf = sortOf . tcConCon


unitCon, trueCon, falseCon, nilCon, consCon :: Con p
unitCon  = BuiltinCon UnitCon
trueCon  = BuiltinCon TrueCon
falseCon = BuiltinCon FalseCon
nilCon   = BuiltinCon NilCon
consCon  = BuiltinCon ConsCon

tcUnitCon, tcTrueCon, tcFalseCon, tcNilCon, tcConsCon :: IsTc p => TcCon p
tcUnitCon  = TcCon unitCon unitTyCon
tcTrueCon  = TcCon trueCon boolTyCon
tcFalseCon = TcCon falseCon boolTyCon
tcNilCon   = TcCon nilCon listTyCon
tcConsCon  = TcCon consCon listTyCon


-- * Operators

instance IsTc p => Sorted Op (Sigma p) where
  sortOf (BoolOp bop) = sortOf bop
  sortOf (IntOp iop)  = sortOf iop
  sortOf CONSOp       = sortOf ConsCon

instance IsTc p => Sorted BoolOp (Sigma p) where
  sortOf NotB = boolTy --> boolTy
  sortOf OrB = boolTy --> boolTy --> boolTy
  sortOf AndB = boolTy --> boolTy --> boolTy
  sortOf ImpB = boolTy --> boolTy --> boolTy
  sortOf IffB = boolTy --> boolTy --> boolTy
  sortOf EqB  = mkForallTy [a_tv] $ a --> a --> boolTy
    where a_nm = mkUsrName (mkOccName TyVarNS "a") a_uniq
          a_uniq = -21
          a_tv = TyV a_nm typeKi False
          a = VarTy a_tv
  sortOf NeqB  = mkForallTy [a_tv] $ a --> a --> boolTy
    where a_nm = mkUsrName (mkOccName TyVarNS "a") a_uniq
          a_uniq = -22
          a_tv = TyV a_nm typeKi False
          a = VarTy a_tv
  sortOf LtB = intTy --> intTy --> boolTy
  sortOf LeB = intTy --> intTy --> boolTy
  sortOf GtB = intTy --> intTy --> boolTy
  sortOf GeB = intTy --> intTy --> boolTy

  -- NB: / and % could be more specific but that would introduce a mutually 
  --     recursive dependency between both. This dependency may be OK since 
  --     they are built-in, but since the language does not allow you to do
  --     that.. we don't allow that as well.
  --     We *may* provide some assumed theorems, for instance
  --        @theorem div_mod = forall n m, (n/m) * m + (n%m) == n@
  --     as well as some useful type judgements once we add support for them.
instance IsTc p => Sorted IntOp (Sigma p) where
  sortOf NegI = intTy --> intTy
  sortOf AddI = intTy --> intTy --> intTy
  sortOf SubI = intTy --> intTy --> intTy
  sortOf MulI = intTy --> intTy --> intTy
  sortOf DivI = intTy
                  --> mkDomVar m intTy (Var m !=* zero)
                  @--> intTy
    where m = mkVarId m_nm intTy
          m_nm = mkSysName (mkOccName VarNS "m") m_uniq
          m_uniq = -31
  sortOf ModI = intTy
                  --> mkDomVar m intTy (Var m !=* zero)
                  @--> intTy
    where m = mkVarId m_nm intTy
          m_nm = mkSysName (mkOccName VarNS "m") m_uniq
          m_uniq = -32
  sortOf ExpI = intTy --> intTy --> intTy


notOp, orOp, andOp, impOp, iffOp :: Op
eqOp, neqOp, ltOp, leOp, gtOp, geOp :: Op
notOp = BoolOp NotB
orOp  = BoolOp OrB
andOp = BoolOp AndB
impOp = BoolOp ImpB
iffOp = BoolOp IffB
eqOp  = BoolOp EqB
neqOp = BoolOp NeqB
ltOp  = BoolOp LtB
leOp  = BoolOp LeB
gtOp  = BoolOp GtB
geOp  = BoolOp GeB

negOp, addOp, subOp, mulOp, divOp, modOp, expOp :: Op
negOp = IntOp NegI
addOp = IntOp AddI
subOp = IntOp SubI
mulOp = IntOp MulI
divOp = IntOp DivI
modOp = IntOp ModI
expOp = IntOp ExpI
