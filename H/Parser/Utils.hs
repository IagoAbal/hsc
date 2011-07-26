{-# LANGUAGE GADTs #-}


-- #hide
-----------------------------------------------------------------------------
-- |
-- Module      :  H.Parser.Utils
-- Copyright   :  (c) The GHC Team, 1997-2000
--                (c) Iago Abal, 2011
-- License     :  BSD-style (see the file libraries/base/LICENSE)
-- 
-- Maintainer  :  iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Utilities for the H! parser.
--
-----------------------------------------------------------------------------

module H.Parser.Utils
  where

import H.Syntax
import H.Phase
import H.Parser.ParseMonad
import H.Pretty

import Data.List ( nub )


data TyParamsContext = TypeDeclTPC (TyNAME Pr)
                     | DataDeclTPC (TyNAME Pr)
                     | ForallTyTPC

checkTyParams :: SrcLoc -> TyParamsContext -> TyParams Pr -> P ()
checkTyParams loc ctx typs
  | nub typs == typs = return ()
  -- there is some repeated variable as in (for example) @forall a a b. [(a,b)]@
  | otherwise        = fail ("Duplicated type variable(s) in " ++ pp_ctx ctx )
                        `atSrcLoc` loc
  where pp_ctx (TypeDeclTPC nm) = "`" ++ prettyPrint nm ++ "' type declaration"
        pp_ctx (DataDeclTPC nm) = "`" ++ prettyPrint nm ++ "' data declaration"
        pp_ctx ForallTyTPC      = "'forall' type"

-- -----------------------------------------------------------------------------
-- -- Various Syntactic Checks



-- -----------------------------------------------------------------------------
-- -- Checking Patterns.


-- -----------------------------------------------------------------------------
-- -- Check Expression Syntax

-- checkExpr :: HsExp -> P HsExp
-- checkExpr e = case e of
--  HsVar _       -> return e
--  HsCon _       -> return e
--  HsLit _       -> return e
--  HsInfixApp e1 op e2   -> check2Exprs e1 e2 (flip HsInfixApp op)
--  HsApp e1 e2     -> check2Exprs e1 e2 HsApp
--  HsNegApp e      -> check1Expr e HsNegApp
--  HsLambda loc ps e   -> check1Expr e (HsLambda loc ps)
--  HsLet bs e      -> check1Expr e (HsLet bs)
--  HsIf e1 e2 e3     -> check3Exprs e1 e2 e3 HsIf
--  HsCase e alts     -> do
--             alts <- mapM checkAlt alts
--             e <- checkExpr e
--             return (HsCase e alts)
--  HsDo stmts      -> do
--             stmts <- mapM checkStmt stmts
--             return (HsDo stmts)
--  HsTuple es      -> checkManyExprs es HsTuple
--  HsList es     -> checkManyExprs es HsList
--  HsParen e     -> check1Expr e HsParen
--  HsLeftSection e op    -> check1Expr e (flip HsLeftSection op)
--  HsRightSection op e   -> check1Expr e (HsRightSection op)
--  HsRecConstr c fields    -> do
--             fields <- mapM checkField fields
--             return (HsRecConstr c fields)
--  HsRecUpdate e fields    -> do
--             fields <- mapM checkField fields
--             e <- checkExpr e
--             return (HsRecUpdate e fields)
--  HsEnumFrom e      -> check1Expr e HsEnumFrom
--  HsEnumFromTo e1 e2    -> check2Exprs e1 e2 HsEnumFromTo
--  HsEnumFromThen e1 e2      -> check2Exprs e1 e2 HsEnumFromThen
--  HsEnumFromThenTo e1 e2 e3 -> check3Exprs e1 e2 e3 HsEnumFromThenTo
--  HsListComp e stmts        -> do
--             stmts <- mapM checkStmt stmts
--             e <- checkExpr e
--             return (HsListComp e stmts)
--  HsExpTypeSig loc e ty     -> do
--             e <- checkExpr e
--             return (HsExpTypeSig loc e ty)
--  _                         -> fail "Parse error in expression"

-- -- type signature for polymorphic recursion!!
-- check1Expr :: HsExp -> (HsExp -> a) -> P a
-- check1Expr e1 f = do
--  e1 <- checkExpr e1
--  return (f e1)

-- check2Exprs :: HsExp -> HsExp -> (HsExp -> HsExp -> a) -> P a
-- check2Exprs e1 e2 f = do
--  e1 <- checkExpr e1
--  e2 <- checkExpr e2
--  return (f e1 e2)

-- check3Exprs :: HsExp -> HsExp -> HsExp -> (HsExp -> HsExp -> HsExp -> a) -> P a
-- check3Exprs e1 e2 e3 f = do
--  e1 <- checkExpr e1
--  e2 <- checkExpr e2
--  e3 <- checkExpr e3
--  return (f e1 e2 e3)

-- checkManyExprs :: [HsExp] -> ([HsExp] -> a) -> P a
-- checkManyExprs es f = do
--  es <- mapM checkExpr es
--  return (f es)

-- checkAlt :: HsAlt -> P HsAlt
-- checkAlt (HsAlt loc p galts bs) = do
--  galts <- checkGAlts galts
--  return (HsAlt loc p galts bs)

-- checkGAlts :: HsGuardedAlts -> P HsGuardedAlts
-- checkGAlts (HsUnGuardedAlt e) = check1Expr e HsUnGuardedAlt
-- checkGAlts (HsGuardedAlts galts) = do
--  galts <- mapM checkGAlt galts
--  return (HsGuardedAlts galts)

-- checkGAlt :: HsGuardedAlt -> P HsGuardedAlt
-- checkGAlt (HsGuardedAlt loc e1 e2) = check2Exprs e1 e2 (HsGuardedAlt loc)

-- checkStmt :: HsStmt -> P HsStmt
-- checkStmt (HsGenerator loc p e) = check1Expr e (HsGenerator loc p)
-- checkStmt (HsQualifier e) = check1Expr e HsQualifier
-- checkStmt s@(HsLetStmt _) = return s

-- checkField :: HsFieldUpdate -> P HsFieldUpdate
-- checkField (HsFieldUpdate n e) = check1Expr e (HsFieldUpdate n)

-- -----------------------------------------------------------------------------
-- -- Check Equation Syntax

-- checkValDef :: SrcLoc -> Exp Pr -> Rhs Pr -> [Decl Fn Pr] -> P (Decl Fn Pr)
-- checkValDef srcloc lhs rhs whereBinds
--   = case isFunLhs lhs [] of
--          Just (f,es) -> do
--             ps <- mapM checkPattern es
--             return (HsFunBind [HsMatch srcloc f ps rhs whereBinds])
--          Nothing     -> do
--            lhs <- checkPattern lhs
--            return (HsPatBind srcloc lhs rhs whereBinds)

-- -- A variable binding is parsed as a PatBind.

-- isFunLhs :: Exp Pr -> [Exp Pr] -> Maybe (NAME Pr, [Exp Pr])
-- isFunLhs (App (Var (UnQual f)) e) es = Just (f, e:es)
-- isFunLhs (App (Paren f) e) es = isFunLhs f (e:es)
-- isFunLhs (App f e) es = isFunLhs f (e:es)
-- isFunLhs _ _ = Nothing


-----------------------------------------------------------------------------
-- Reverse a list of declarations, merging adjacent HsFunBinds of the
-- same name and checking that their arities match.

checkRevDecls :: [AnyDecl Pr] -> P [AnyDecl Pr]
checkRevDecls = mergeFunBinds []
  where
      mergeFunBinds :: [AnyDecl Pr] -> [AnyDecl Pr] -> P [AnyDecl Pr]
      mergeFunBinds revDs [] = return revDs
      mergeFunBinds revDs (AnyDecl (FunBind _ name ms1@(Match _ ps _:_)):ds1)
        = mergeMatches ms1 ds1
          where
              arity = length ps
              mergeMatches :: [Match Pr] -> [AnyDecl Pr] -> P [AnyDecl Pr]
              mergeMatches ms' (AnyDecl (FunBind _ name' ms@(Match loc ps' _:_)):ds)
                | name' == name =
                    if length ps' /= arity
                      then fail ("arity mismatch for '" ++ prettyPrint name ++ "'")
                              `atSrcLoc` loc
                      else mergeMatches (ms++ms') ds
              mergeMatches ms' ds = mergeFunBinds (AnyDecl (FunBind Rec name ms'):revDs) ds
      mergeFunBinds revDs (d:ds) = mergeFunBinds (d:revDs) ds


checkRevFnDecls :: [Decl Fn Pr] -> P [Decl Fn Pr]
checkRevFnDecls = mergeFunBinds []
  where
      mergeFunBinds :: [Decl Fn Pr] -> [Decl Fn Pr] -> P [Decl Fn Pr]
      mergeFunBinds revDs [] = return revDs
      mergeFunBinds revDs (FunBind _ name ms1@(Match _ ps _:_):ds1)
        = mergeMatches ms1 ds1
          where
              arity = length ps
              mergeMatches :: [Match Pr] -> [Decl Fn Pr] -> P [Decl Fn Pr]
              mergeMatches ms' (FunBind _ name' ms@(Match loc ps' _:_):ds)
                | name' == name =
                    if length ps' /= arity
                      then fail ("arity mismatch for '" ++ prettyPrint name ++ "'")
                              `atSrcLoc` loc
                      else mergeMatches (ms++ms') ds
              mergeMatches ms' ds = mergeFunBinds (FunBind Rec name ms':revDs) ds
      mergeFunBinds revDs (d:ds) = mergeFunBinds (d:revDs) ds
