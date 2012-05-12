
{-# LANGUAGE CPP  #-}

module H.Prop where

import H.Syntax

import Data.List  ( sort )

#include "bug.h"


_True_ :: IsTc p => Prop p
_True_ = Con tcTrueCon

_False_ :: IsTc p => Prop p
_False_ = Con tcFalseCon

bool :: IsTc p => Prop p -> Maybe Bool
bool (Con con)
  | con == tcTrueCon  = Just True
  | con == tcFalseCon = Just False
bool _other           = Nothing

infixr .==>.

notP :: Prop p -> Prop p
notP (PrefixApp (Op (BoolOp NotB)) p) = p
notP p                                = PrefixApp (Op notOp) p

(.&&.), (.||.), (.==>.), (.<=>.) :: Prop p -> Prop p -> Prop p
p .&&. q = InfixApp p (Op andOp) q
p .||. q = InfixApp p (Op orOp) q
p .==>. q = InfixApp p (Op impOp) q
p .<=>. q = InfixApp p (Op iffOp) q

mkForall :: [QVar p] -> Prop p -> Prop p
mkForall [] prop = prop
mkForall vs prop = QP ForallQ vs prop

hypo :: IsTc p => Prop p -> Prop p -> Prop p
hypo (Con con) q
  | con == tcTrueCon = q
  | con == tcFalseCon = _True_
hypo p q = p .==>. q

-- | Splits a proposition into conjunctions
-- e.g. @splitAnd (p1 && p2 && ... && pN) == [p1,p2,...,pN]@
splitConj :: Prop p -> [Prop p]
splitConj (InfixApp p (Op (BoolOp AndB)) q)
  = splitConj p ++ splitConj q
splitConj p = [p]

conj :: IsTc p => [Prop p] -> Prop p
conj [] = _True_
conj ps = foldr1 (.&&.) ps

disj :: IsTc p => [Prop p] -> Prop p
disj [] = _False_
disj ps = foldr1 (.||.) ps

hypos :: IsTc p => [Prop p] -> Prop p -> Prop p
hypos [] p = p
hypos hs p = hypo (conj hs) p

mkConj :: [Prop p] -> Maybe (Prop p)
mkConj [] = Nothing
mkConj ps = Just $ foldr1 (.&&.) ps


filterProp :: (Prop p -> Bool) -> Prop p -> Maybe (Prop p)
filterProp p = mkConj . filter p . splitConj

oneOfInts :: IsTc p => Exp p -> [Integer] -> Prop p
oneOfInts _t []  = _False_
oneOfInts  t [n] = t ==* mkInt n
oneOfInts  t ns1 = disj $ build_prop $ sort ns1
  where
    build_prop ns@(a:rest)
      | ns == [a..b] = [mkInt a .<=. t .&&. t .<=. mkInt b]
      | otherwise    = [t ==* mkInt n | n <- ns]
      where b = last rest
    build_prop _other = impossible
