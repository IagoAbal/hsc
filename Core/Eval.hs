
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}

module Core.Eval
  ( eval )
  where

import Core.Syntax
import Core.Syntax.Freshen ( freshenExp )
import Core.Syntax.Subst1.Direct ( substExp, substRhs )

import Name
import Pretty
import Unique ( MonadUnique(..), Unique, evalUnique, mkSupply )

import Control.Monad.State
import Data.Functor ( (<$>) )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( isNothing )
import Data.Generics.Uniplate.Data ( universeBi )

#include "bug.h"


type Heap = Map Var Exp

newtype EvalM a = EvalM { unEvalM :: StateT Heap Unique a }
  deriving Monad

instance MonadUnique EvalM where
  getUniq = EvalM $ lift getUniq
  forkSupply = EvalM $ lift forkSupply

heapRm :: Var -> EvalM ()
heapRm = EvalM . modify . Map.delete

heapAdd :: Var -> Exp -> EvalM ()
heapAdd x = EvalM . modify . Map.insert x

heapLookup :: Var -> EvalM Exp
heapLookup x = EvalM $ do
  heap <- get
  case Map.lookup x heap of
      Just e  -> return e
      Nothing -> error "eval: fatal error"

heapAddBind :: Bind -> EvalM ()
heapAddBind (FunBind _ f tvs xs rhs)
  = heapAdd f $ mkTyLam tvs $ mkLam xs rhs

heapAddBinds :: [Bind] -> EvalM ()
heapAddBinds = mapM_ heapAddBind

redVar :: Var -> EvalM Value
redVar x = do
--   traceDoc (text "redVar" <+> pretty x) $ do
  e <- heapLookup x
--   traceDoc (text "> redVar e=" <+> pretty e) $ do
  heapRm x
  e' <- red e
--   traceDoc (text "> redVar e'" <+> pretty e') $ do
  heapAdd x e'
  let ?varMap = Map.empty in freshenExp e'

betaVar :: Value -> Var -> Value
betaVar (Lam    [x] (Rhs  _ t)) y = substExp [(x,Var y)] [] t
betaVar (Lam (x:xs)        rhs) y
  = Lam xs $ substRhs [(x,Var y)] [] rhs
betaVar _e1 _y = bug "betaVar: not a beta-redex"

redApp :: Value -> Exp -> EvalM Value
redApp f@(Lam _ _)     (Var y) = red $ betaVar f y
redApp f@(Lam (x:_) _) e = do
  z <- newVarFrom x
  heapAdd z e
  red $ betaVar f z
  -- assuming f is a constructor
redApp f e = return $ App f e

redTyApp :: Value -> [Tau] -> Value
redTyApp (TyLam tvs t) tys = substExp [] (zip tvs tys) t
  -- assuming f is a constructor
redTyApp f             tys = TyApp f tys

redIf :: [GuardedRhs] -> Maybe Exp -> EvalM Value
redIf [] Nothing = error "fatal error, if exhausted"
redIf [] (Just e) = red e
redIf (GuardedRhs g1 e:grhss) mbExp = if_ =<< red g1
  where if_ g | g == mkTrue  = red e
              | g == mkFalse = redIf grhss mbExp
        if_ _g = bug "red"

match_var :: Exp -> SPat -> (Var,Exp)
match_var e (VarPat x) = (x,e)
match_var _e _p = bug "match_var"

match :: Exp -> SPat -> Maybe [(Var,Exp)]
match e        (VarPat x) = Just [(x,e)]
match (Lit l1) (LitPat l2) | l1 == l2 = Just []
match (List _ []) (ConPat _ _ []) = Just []
match (InfixApp x (OpExp _ CONSOp) xs) (ConPat _ _ [y,ys])
  = Just [match_var x y,match_var xs ys]
match (List ty (x:xs)) (ConPat _ _ [y,ys])
  = Just [match_var x y,match_var (List ty xs) ys]
match (splitApp -> (TyApp (Con con1) _,es)) (ConPat _ con2 ps)
  | con1 == con2 = Just $ zipWith match_var es ps
match (splitApp -> (Con con1,es)) (ConPat _ con2 ps)
  | con1 == con2 = Just $ zipWith match_var es ps
match (Tuple _ es) (TuplePat _ ps) = Just $ zipWith match_var es ps
match _p1 _p2 = Nothing

redCase :: Exp -> [Alt] -> EvalM Exp
redCase _scrut [] = error "fatal error, case exhausted"
redCase scrut (Alt pat (Rhs _ e):alts)
  = -- traceDoc (text "redCase scrut=" <> pretty scrut <+> text "pat =" <> pretty pat) $ do
    case match scrut pat of
        Nothing -> redCase scrut alts
        Just bs -> do
--           traceDoc (text "redCase branch=" <> pretty e) $ do
          mapM_ (uncurry heapAdd) bs
          red' e

matchPat :: Exp -> Pat -> Maybe [(Var,Exp)]
matchPat e (VarPat x) = Just [(x,e)]
matchPat (Lit l1) (LitPat l2) | l1 == l2 = Just []
matchPat (List _ []) (ConPat _ _ []) = Just []
matchPat (InfixApp x (OpExp _ CONSOp) xs) (ConPat _ _ [y,ys]) = do
  bs1 <- matchPat x y
  bs2 <- matchPat xs y
  return $ bs1 ++ bs2
matchPat (List ty (x:xs)) (ConPat _ _ [y,ys]) = do
  bs1 <- matchPat x y
  bs2 <- matchPat (List ty xs) y
  return $ bs1 ++ bs2
matchPat (splitApp -> (TyApp (Con con1) _,es)) (ConPat _ con2 ps)
  | con1 == con2 = concat <$> zipWithM matchPat es ps
matchPat (Tuple _ es) (TuplePat _ ps) = concat <$> zipWithM matchPat es ps
matchPat _p1 _p2 = Nothing

redLetP :: Pat -> Exp -> Prop -> EvalM Prop
redLetP pat expr prop
  = case matchPat expr pat of
        Nothing -> return mkFalse
        Just bs -> do
          mapM_ (uncurry heapAdd) bs
          red' prop

redEq :: Exp -> Exp -> EvalM Exp
redEq e1 e2 = do
  e1' <- red' e1
  e2' <- red' e2
--   traceDoc (text "redEq... e1=" <> pretty e1' <+> text "e2=" <> pretty e2') $ do
  go e1' e2'
  where go (Lit l1) (Lit l2) = return $ bool2exp $ l1 == l2
        go (Tuple _ es1) (Tuple _ es2) = do
          es_eq <- zipWithM (\e1 e2 -> liftM val2bool $ redEq e1 e2) es1 es2
          return $ bool2exp $ and es_eq
        go (isNilList -> True) (isNilList -> True) = return $ mkTrue
        go (isNilList -> True) (isNilList -> False) = return $ mkFalse
        go (isNilList -> False) (isNilList -> True) = return $ mkFalse
        go (isConsList -> Just(x,xs)) (isConsList -> Just(y,ys)) = do
          x' <- red x
          y' <- red y
          if x' == y' then redEq xs ys
                      else return mkFalse
        go (splitApp -> (TyApp (Con con1) _,es1)) (splitApp -> (TyApp (Con con2) _,es2))
          | con1 == con2 = do
            es_eq <- zipWithM (\e1 e2 -> liftM val2bool $ redEq e1 e2) es1 es2
            return $ bool2exp $ and es_eq
          | otherwise = return mkFalse
        go (splitApp -> (Con con1,es1)) (splitApp -> (Con con2,es2))
          | con1 == con2 = do
            es_eq <- zipWithM (\e1 e2 -> liftM val2bool $ redEq e1 e2) es1 es2
            return $ bool2exp $ and es_eq
          | otherwise = return mkFalse
        go e1 e2 = traceDoc (text "redEq... e1=" <> pretty e1 <+> text "e2=" <> pretty e2) $ error "unsupported"

redNot e1 | e1 == mkTrue  = mkFalse
redNot e1 | e1 == mkFalse = mkTrue
redNot _e1 = bug "red"

red :: Exp -> EvalM Value
red (Var x) = redVar x
red (Par x) = redVar x
red e@(Con _) = return e
red e@(Lit _) = return e
red (PrefixApp (OpExp [] (BoolOp NotB)) e) = liftM redNot $ red e
red (PrefixApp (OpExp [] (IntOp NegI)) e) = liftM neg_ $ red e
  where neg_ (Lit (IntLit n)) = mkInt $ -n
        neg_ _e1 = bug "red"
red (InfixApp e1 (OpExp [] (BoolOp bop)) e2)
  | bop `elem` [OrB, AndB, ImpB, IffB] = do
    e1' <- red e1
    bool_ bop e1' e2
  where bool_ OrB t1 _t2' | t1 == mkTrue  = return mkTrue
        bool_ OrB t1  t2' | t1 == mkFalse = red t2'
        bool_ AndB t1 _t2' | t1 == mkFalse = return mkFalse
        bool_ AndB t1  t2' | t1 == mkTrue  = red t2'
        bool_ ImpB t1 _t2' | t1 == mkFalse = return mkTrue
        bool_ ImpB t1  t2' | t1 == mkTrue  = red t2'
        bool_ IffB t1  t2' = do
          t2 <- red t2'
          return $ if t1 == t2 then mkTrue else mkFalse
        bool_ _bop _t1 _t2 = bug "red"
red (InfixApp e1 (OpExp [] (BoolOp bop)) e2)
  | bop `elem` [LtB, LeB, GtB, GeB] = do
    Lit (IntLit i1) <- red e1
    Lit (IntLit i2) <- red e2
    return $ cmp_ bop i1 i2
  where cmp_ LtB n m
          | n < m     = mkTrue
          | otherwise = mkFalse
        cmp_ LeB n m
          | n <= m     = mkTrue
          | otherwise  = mkFalse
        cmp_ GtB n m
          | n > m     = mkTrue
          | otherwise = mkFalse
        cmp_ GeB n m
          | n >= m     = mkTrue
          | otherwise  = mkFalse
        cmp_ _cop _n _m = bug "red"
red (InfixApp e1 (OpExp [ty] (BoolOp bop)) e2)
                                  -- should be aware of type synonyms
  | bop `elem` [EqB, NeqB] && isNothing (isFunTy ty) = cmp_ bop e1 e2
  where cmp_ EqB   = redEq
        cmp_ NeqB  = \e1 e2 -> liftM redNot $ redEq e1 e2
        cmp_ _     = bug "red"
red (InfixApp e1 (OpExp [] (IntOp iop)) e2) = do
  Lit (IntLit i1) <- red' e1
  Lit (IntLit i2) <- red' e2
  return $ arith_ iop i1 i2
  where arith_ AddI n m = mkInt $ n+m
        arith_ SubI n m = mkInt $ n-m
        arith_ MulI n m = mkInt $ n*m
        arith_ DivI n m = mkInt $ n `div` m
        arith_ ModI n m = mkInt $ n `mod` m
        arith_ ExpI n m = mkInt $ n^m
        arith_ _ _t1 _t2 = bug "red"
red e@(InfixApp _ (OpExp _ CONSOp) _) = return e
red (App f e) = do
  f' <- red' f
--   traceDoc (text "red-App f'=" <+> pretty f') $ do
  redApp f' e
red (TyApp f e) = do
  f' <- red f
  return $ redTyApp f' e
red e@(Lam _ _) = return e
red (Let bs e) = do
  heapAddBinds bs
  red e
red e@(TyLam _ _) = return e
red (Ite _ty g1 e1 e2) = ite_ =<< red g1
  where ite_ g | g == mkTrue  = red e1
               | g == mkFalse = red e2
        ite_ _g = bug "red"
red (If _ (GuardedRhss grhss mbExp)) = redIf grhss mbExp
red (Case _ scrut alts) = do
  scrut' <- red scrut
  redCase scrut' alts
red (Tuple ty es) = liftM (Tuple ty) $ mapM red es
red (List ty es) = liftM (List ty) $ mapM red es
red (Paren e) = red e
red (EnumFromTo e1 e2) = do
  Lit (IntLit i1) <- red e1
  Lit (IntLit i2) <- red e2
  return $ mkIntList [i1..i2]
red (EnumFromThenTo e1 e2 e3) = do
  Lit (IntLit i1) <- red e1
  Lit (IntLit i2) <- red e2
  Lit (IntLit i3) <- red e3
  return $ mkIntList [i1,i2..i3]
red (Coerc e _) = red e
red (LetP pat e p) = do
  e' <- red e
  redLetP pat e' p
red e@(QP _ _ _) = return e
red e = traceDoc (text "red e=" <+> pretty e) $ error "unsupported"

red' e = {- traceDoc (text "red e=" <+> pretty e) $ -} red e

eval :: Module -> [(Var,Exp)] -> Exp -> Exp
eval mod input expr
  = evalUnique (evalStateT (unEvalM red_expr) (Map.fromList input)) uniq_supply
  where red_expr = do
          heapAddTopBinds mod
          red' expr
        uniq_supply = mkSupply uniq_seed
        uniq_seed = 1 + maximum [ nameUniq n | n <- universeBi mod ]
        heapAddTopBinds = go . modDecls
          where go [] = return ()
                go (ValDecl b:ds) = heapAddBind b >> go ds
                go (_:ds) = go ds
