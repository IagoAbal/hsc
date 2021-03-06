
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  H.Parser.Fixity
-- Copyright   :  (c) Niklas Broberg 2009
--                (c) Iago Abal 2011
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Iago Abal, iago.abal@gmail.com
-- Stability   :  stable
-- Portability :  portable
--
-- Fixity information to give the parser so that infix operators can
-- be parsed properly.
--
-----------------------------------------------------------------------------
module H.Parser.Fixity
    ( applyPreludeFixities
    ) where

import H.Syntax

import Control.Monad ( when, (<=<), liftM, liftM2, liftM3 )
import Data.Traversable (mapM)
import Prelude hiding (mapM)

#include "bug.h"



applyPreludeFixities :: Monad m => Module Pr -> m (Module Pr)
applyPreludeFixities = applyFixities preludeFixities

------


-- | Associativity of an operator.
data Assoc
   = AssocNone  -- ^ non-associative operator (declared with @infix@)
   | AssocLeft  -- ^ left-associative operator (declared with @infixl@)
   | AssocRight -- ^ right-associative operator (declared with @infixr@)
   deriving(Eq,Ord,Show)

-- | Operator fixities are represented by their associativity
--   (left, right or none) and their precedence (0-9).
data Fixity = Fixity Assoc Int Op
  deriving (Eq,Ord)

-- | All AST elements that may include expressions which in turn may
--   need fixity tweaking will be instances of this class.
class AppFixity ast where
  -- | Tweak any expressions in the element to account for the
  --   fixities given. Assumes that all operator expressions are
  --   fully left associative chains to begin with.
  applyFixities :: Monad m => [Fixity] -- ^ The fixities to account for.
                    -> ast  -- ^ The element to tweak.
                    -> m ast  -- ^ The same element, but with operator expressions updated, or a failure.


instance AppFixity (Exp Pr) where
  applyFixities fixs = infFix fixs <=< leafFix fixs
    where -- This is the real meat case. We can assume a left-associative list to begin with.
          infFix fixs (InfixApp a (Op op2) z) = do
              e <- infFix fixs a
              case e of
               InfixApp x (Op op1) y -> do
                  let (a1,p1) = askFixity fixs op1
                      (a2,p2) = askFixity fixs op2
                  when (p1 == p2 && (a1 /= a2 || a1 == AssocNone)) -- Ambiguous infix expression!
                    $ fail "Ambiguous infix expression"
                  if (p1 > p2 || p1 == p2 && (a1 == AssocLeft || a2 == AssocNone)) -- Already right order
                   then return $ InfixApp e (Op op2) z
                   else liftM (InfixApp x (Op op1)) (infFix fixs $ InfixApp y (Op op2) z)
               _  -> return $ InfixApp e (Op op2) z

          infFix _ e = return e

instance AppFixity (Pat Pr) where
  applyFixities fixs = leafFixP fixs

instance AppFixity (QVar Pr) where
  applyFixities _fixs v@(QVar _n Nothing)  = return v
  applyFixities  fixs   (QVar n (Just ty)) = do
    ty' <- applyFixities fixs ty
    return $ QVar n (Just ty')

-- Internal: lookup associativity and precedence of an operator
askFixity :: [Fixity] -> Op -> (Assoc, Int)
askFixity xs op = askFix xs op -- undefined -- \k -> askFixityP xs (f k) -- lookupWithDefault (AssocLeft, 9) (f k) mp

askFix :: [Fixity] -> Op -> (Assoc, Int)
askFix xs = \k -> lookupWithDefault (AssocLeft, 9) k mp
    where
        lookupWithDefault def k mp = case lookup k mp of
            Nothing -> def
            Just x  -> x

        mp = [(x,(a,p)) | Fixity a p x <- xs]


-- -- | All fixities defined in the Prelude.
preludeFixities :: [Fixity]
preludeFixities = concat
    [infixr_ 8 [expOp]
    ,infixl_ 7 [mulOp, divOp, modOp]
    ,infixl_ 6 [addOp, subOp]
    ,infixr_ 5 [CONSOp]
    ,infix_  4 [eqOp, neqOp, ltOp, leOp, gtOp, geOp]
    ,infixr_ 3 [andOp]
    ,infixr_ 2 [orOp]
    ,infixr_ 1 [impOp, iffOp]
    ]

infixr_, infixl_, infix_ :: Int -> [Op] -> [Fixity]
infixr_ = fixity AssocRight
infixl_ = fixity AssocLeft
infix_  = fixity AssocNone

-- Internal: help function for the above definitions.
fixity :: Assoc -> Int -> [Op] -> [Fixity]
fixity a p = map (Fixity a p)





-------------------------------------------------------------------
-- Boilerplate - yuck!! Everything below here is internal stuff

instance AppFixity (Module Pr) where
    applyFixities fixs (Module loc n decls) =
        liftM (Module loc n) $ mapM (applyFixities fixs) decls

instance AppFixity (Decl Pr) where
  applyFixities fixs decl = case decl of
      TypeDecl loc tynm tyargs ty -> liftM (TypeDecl loc tynm tyargs) (fix ty)
      DataDecl loc tynm tyargs cons -> liftM (DataDecl loc tynm tyargs) (mapM fix cons)
      ValDecl bind -> liftM ValDecl $ fix bind
      GoalDecl loc gname gtype ptctyparams prop ->
          liftM (GoalDecl loc gname gtype ptctyparams) (fix prop)
    where fix :: (Monad m, AppFixity ast) => ast -> m ast
          fix x = applyFixities fixs x

instance AppFixity (Bind Pr) where
  applyFixities fixs bind = case bind of
      FunBind rec n sig None matches  -> liftM3 (FunBind rec n) (fix sig) (return None) (mapM fix matches)
      PatBind loc p rhs -> liftM2 (PatBind loc) (fix p) (fix rhs)
    where fix :: (Monad m, AppFixity ast) => ast -> m ast
          fix x = applyFixities fixs x

instance AppFixity (TypeSig Pr) where
  applyFixities fixs NoTypeSig = return NoTypeSig
  applyFixities fixs (TypeSig loc polyty) = liftM (TypeSig loc) (fix polyty)
    where fix x = applyFixities fixs x

instance AppFixity (ConDecl Pr) where
  applyFixities fixs (ConDeclIn loc con tys)
    = liftM (ConDeclIn loc con) $ mapM (applyFixities fixs) tys
  applyFixities _fixs _other = impossible

instance AppFixity (Match Pr) where
    applyFixities fixs (Match loc ps rhs) = liftM2 (Match loc) (mapM fix ps) (fix rhs)
      where fix :: (Monad m, AppFixity ast) => ast -> m ast
            fix x = applyFixities fixs x

instance AppFixity (Rhs Pr) where
  applyFixities fixs (Rhs None grhs whr)
    = liftM2 (Rhs None) (fix grhs) (mapM fix whr)
    where fix :: (Monad m, AppFixity ast) => ast -> m ast
          fix x = applyFixities fixs x

instance AppFixity (GRhs Pr) where
  applyFixities fixs grhs = case grhs of
      UnGuarded e      -> liftM UnGuarded $ fix e
      Guarded grhss   -> liftM Guarded $ fix grhss
    where fix :: (Monad m, AppFixity ast) => ast -> m ast
          fix x = applyFixities fixs x

instance AppFixity (GuardedRhss Pr) where
  applyFixities fixs (GuardedRhssIn grhss)
    = liftM GuardedRhssIn $ mapM fix grhss
    where fix x = applyFixities fixs x
  applyFixities _fixs _other = impossible

instance AppFixity (GuardedRhs Pr) where
    applyFixities fixs (GuardedRhs loc g e) = liftM2 (GuardedRhs loc) (fix g) $ fix e
      where fix x = applyFixities fixs x



instance AppFixity (Alt Pr) where
    applyFixities fixs (Alt loc p galts) = liftM2 (Alt loc) (fix p) (fix galts)
      where fix :: (Monad m, AppFixity ast) => ast -> m ast
            fix x = applyFixities fixs x

instance AppFixity a => AppFixity (Maybe a) where
  applyFixities fixs Nothing = return Nothing
  applyFixities fixs (Just a) = liftM Just $ applyFixities fixs a

instance AppFixity (Type c Pr) where
  applyFixities fixs ty = case ty of
      VarTy _ -> return ty
      ConTyIn _ -> return ty
      AppTyIn a b -> liftM2 AppTyIn (fix a) (fix b)
      PredTy pat s mbP -> liftM3 PredTy (fix pat) (fix s) (fix mbP)
      FunTy a b -> liftM2 FunTy (fix a) (fix b)
      ListTy a -> liftM ListTy (fix a)
      TupleTy l -> liftM TupleTy $ mapM fix l
      ParenTy a -> liftM ParenTy (fix a)
      ForallTy typarams ty -> liftM (ForallTy typarams) (fix ty)
    where fix :: (Monad m, AppFixity ast) => ast -> m ast
          fix x = applyFixities fixs x

instance AppFixity (Dom Pr) where
  applyFixities fixs (Dom mbPat ty mbProp)
    = liftM3 Dom (fix mbPat) (fix ty) (fix mbProp)
    where fix :: (Monad m, AppFixity ast) => ast -> m ast
          fix x = applyFixities fixs x

-- the boring boilerplate stuff for expressions too
-- Recursively fixes the "leaves" of the infix chains,
-- without yet touching the chain itself. We assume all chains are
-- left-associate to begin with.
leafFix fixs e = case e of
    PrefixApp op e          -> liftM (PrefixApp op) (fix e)
    InfixApp e1 op e2       -> liftM2 (flip InfixApp op) (leafFix fixs e1) (fix e2)
    App e1 e2               -> liftM2 App (fix e1) (fix e2)
    Lam loc pats e       -> liftM2 (Lam loc) (mapM fix pats) $ fix e
    Let bs e                -> liftM2 Let (mapM fix bs) $ fix e
    Ite None e a b       -> liftM3 (Ite None) (fix e) (fix a) (fix b)
    If None grhss                 -> liftM (If None) $ fix grhss
    Case None scrut alts             -> liftM2 (Case None) (fix scrut) $ mapM fix alts
    Tuple None exps              -> liftM (Tuple None) $ mapM fix exps
    List None exps               -> liftM (List None) $ mapM fix  exps
    Paren e                 -> liftM Paren $ fix e
    LeftSection e op        -> liftM (flip LeftSection op) (fix e)
    RightSection op e       -> liftM (RightSection op) $ fix e
    EnumFromTo e1 e2        -> liftM2 EnumFromTo (fix e1) (fix e2)
    EnumFromThenTo e1 e2 e3 -> liftM3 EnumFromThenTo (fix e1) (fix e2) (fix e3)
    Coerc loc e t      -> liftM2 (Coerc loc) (fix e) (fix t)
    QP qt pats prop    -> liftM2 (QP qt) (mapM fix pats) (fix prop)
    _                       -> return e
  where
    fix :: (Monad m, AppFixity ast) => ast -> m ast
    fix x = applyFixities fixs x

leafFixP fixs p = case p of
        InfixCONSPat None p1 p2       -> liftM2 (InfixCONSPat None) (fix p1) (fix p2)
        ConPat None n ps             -> liftM (ConPat None n) $ mapM fix ps
        TuplePat None ps             -> liftM (TuplePat None) $ mapM fix ps
        ListPat None ps              -> liftM (ListPat None) $ mapM fix ps
        ParenPat p              -> liftM ParenPat $ fix p
        AsPat n p            -> liftM (AsPat n) $ fix p
--         SigPat p t    -> liftM2 SigPat (fix p) (fix t)
        _                     -> return p
      where fix :: (Monad m, AppFixity ast) => ast -> m ast
            fix x = applyFixities fixs x
