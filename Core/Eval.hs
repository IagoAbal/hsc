
{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}

module Core.Eval where

import Core.Syntax

import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( isNothing )

#include "bug.h"

#define not_supported (bug "not supported")

type Value = Exp

eval :: (?env :: Map Var Exp) => Exp -> Exp
eval t@(Var x)
  | Just e <- Map.lookup x ?env = eval e
  | otherwise = t
eval t@(Con _) = t
eval t@(Lit _) = t
eval (PrefixApp (OpExp [] (BoolOp NotB)) e) = not_ (eval e)
  where not_ e1 | e1 == mkTrue  = mkFalse
        not_ e1 | e1 == mkFalse = mkTrue
        not_ e1                 = mkNot e1
eval (PrefixApp (OpExp [] (IntOp NegI)) e) = neg_ (eval e)
  where neg_ (Lit (IntLit n)) = mkInt $ -n
        neg_ e1               = mkNeg e1
eval (InfixApp e1 (OpExp [] (BoolOp bop)) e2)
  | bop `elem` [OrB, AndB, ImpB, IffB] = bool_ bop (eval e1) e2
  where bool_ OrB t1 _t2' | t1 == mkTrue  = mkTrue
        bool_ OrB t1  t2' | t1 == mkFalse = eval t2'
        bool_ AndB t1 _t2' | t1 == mkFalse = mkFalse
        bool_ AndB t1  t2' | t1 == mkTrue  = eval t2'
        bool_ ImpB t1 _t2' | t1 == mkFalse = mkTrue
        bool_ ImpB t1  t2' | t1 == mkTrue  = eval t2'
        bool_ IffB t1@(Con _)  t2'
          | t2@(Con _) <- eval t2' = if t1 == t2 then mkTrue else mkFalse
        bool_ _ t1 t2' = mkMonoInfixApp (BoolOp bop) t1 t2'
eval (InfixApp e1 (OpExp [] (BoolOp bop)) e2)
  | bop `elem` [LtB, LeB, GtB, GeB] = cmp_ bop (eval e1) (eval e2)
  where cmp_ LtB (Lit (IntLit n)) (Lit (IntLit m))
          | n < m     = mkTrue
          | otherwise = mkFalse
        cmp_ LeB (Lit (IntLit n)) (Lit (IntLit m))
          | n <= m     = mkTrue
          | otherwise  = mkFalse
        cmp_ GtB (Lit (IntLit n)) (Lit (IntLit m))
          | n > m     = mkTrue
          | otherwise = mkFalse
        cmp_ GeB (Lit (IntLit n)) (Lit (IntLit m))
          | n >= m     = mkTrue
          | otherwise  = mkFalse
        cmp_ _ t1 t2 = mkMonoInfixApp (BoolOp bop) t1 t2
eval (InfixApp e1 (OpExp [ty] (BoolOp bop)) e2)
                                  -- should be aware of type synonyms
  | bop `elem` [EqB, NeqB] && not (isFunTy ty) = cmp_ bop (eval e1) (eval e2)
  where cmp_ EqB t1 t2
          | t1 == t2   = mkTrue
          | otherwise  = mkFalse
        cmp_ NeqB t1 t2
          | t1 /= t2   = mkTrue
          | otherwise  = mkFalse
        cmp_ _ t1 t2 = InfixApp t1 (OpExp [ty] (BoolOp bop)) t2
eval (InfixApp e1 (OpExp [] (IntOp iop)) e2) = arith_ iop (eval e1) (eval e2)
  where arith_ AddI (Lit (IntLit n)) (Lit (IntLit m)) = mkInt $ n+m
        arith_ SubI (Lit (IntLit n)) (Lit (IntLit m)) = mkInt $ n-m
        arith_ MulI (Lit (IntLit n)) (Lit (IntLit m)) = mkInt $ n*m
        arith_ DivI (Lit (IntLit n)) (Lit (IntLit m)) = mkInt $ n `div` m
        arith_ ModI (Lit (IntLit n)) (Lit (IntLit m)) = mkInt $ n `mod` m
        arith_ ExpI (Lit (IntLit n)) (Lit (IntLit m)) = mkInt $ n^m
        arith_ _ t1 t2 = mkMonoInfixApp (IntOp iop) t1 t2
eval (App _ _) = not_supported
eval (TyApp _ _) = not_supported
eval (Lam _ _) = not_supported
eval (Let _ _) = not_supported
eval (TyLam _ _) = not_supported
eval (Ite ty guard e1 e2) = ite_ (eval guard)
  where ite_ g | g == mkTrue  = eval e1
               | g == mkFalse = eval e2
               | otherwise    = Ite ty g e1 e2
eval (If _ _) = not_supported
eval (Case _ _ _) = not_supported
eval (Tuple ty es) = Tuple ty $ map eval es
eval (List ty es) = List ty $ map eval es
eval (Paren e) = eval e
eval (EnumFromTo _ _) = not_supported
eval (EnumFromThenTo _ _ _) = not_supported
eval (Coerc e _) = eval e
eval (QP _ _ _) = not_supported
eval _other = impossible
