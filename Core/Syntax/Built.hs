
{- TODO: Remove unconstrained terms

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

import qualified Util.Set as Set

import Data.Foldable ( toList )
import qualified Data.Generics.Uniplate.Data as G
import qualified Data.Set as Set



-- * Expressions

val2bool :: Value -> Bool
val2bool t | t == mkTrue  = True
           | t == mkFalse = False
val2bool _other = undefined -- bug

bool2exp :: Bool -> Exp
bool2exp True = mkTrue
bool2exp False = mkFalse

filterVars :: Exp -> [Var] -> [Var]
filterVars e xs = go [] (reverse xs) e_fv
  where e_fv = fvExp e
        go acc []     _fvs = acc
        go acc (y:ys)  fvs
          | y `Set.member` fvs = go (y:acc) ys (y_fv `Set.union` fvs)
          | otherwise          = go acc ys fvs
          where y_fv = fvBndr y

cleanup :: Exp -> Exp
cleanup = G.transform f
  where f (QP qt xs (QP qt1 ys p))
          | qt == qt1 = QP qt (xs ++ ys) p
        f (QP qt xs p) = mkQP qt (filterVars p xs) p
        f (InfixApp e1 (OpExp [] (BoolOp OrB)) e2)
          | e1 == e2      = e1
          | e1 == mkTrue  = mkTrue
          | e2 == mkTrue  = mkTrue
          | e1 == mkFalse = e2
          | e2 == mkFalse = e1
        f (InfixApp e1 (OpExp [] (BoolOp AndB)) e2)
          | e1 == e2 = e1
          | e1 == mkTrue  = e2
          | e2 == mkTrue  = e1
          | e1 == mkFalse = mkFalse
          | e2 == mkFalse = mkFalse
        f (InfixApp e1 (OpExp [] (BoolOp ImpB)) e2)
          | e1 == e2 = mkTrue
          | e1 == mkTrue  = e2
          | e2 == mkTrue  = mkTrue
          | e1 == mkFalse = mkTrue
          | e2 == mkFalse = mkNot e1
        f (InfixApp e1 (OpExp [_] (BoolOp EqB)) e2)
          | e1 == e2 = mkTrue
        f t = t

mkQP :: Quantifier -> [Var] -> Prop -> Prop
mkQP _qt [] prop = prop
mkQP  qt xs prop = QP qt xs prop

mkLet :: [Bind] -> Exp -> Exp
mkLet []    e = e
mkLet binds e = Let binds' e
  where e_fv = fvExp e
        binds' = filter_bs [] (reverse binds) e_fv
        filter_bs acc [] _fvs = acc
        filter_bs acc (b:bs) fvs
          | b_x `Set.member` fvs = filter_bs (b:acc) bs (b_fv `Set.union` fvs)
          | otherwise            = filter_bs acc bs fvs
          where b_x = bsBind b
                b_fv = fvBind b

-- ** Prop

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
