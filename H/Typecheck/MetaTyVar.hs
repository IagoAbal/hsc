{-# LANGUAGE GADTs #-}

module H.Typecheck.MetaTyVar where

import H.Syntax
import H.Phase

import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Foldable as F
import qualified Data.Traversable as T


mtvBinds :: [Bind Tc] -> Set MetaTyVar
mtvBinds = Set.unions . map mtvBind

mtvBind :: Bind Tc -> Set MetaTyVar
mtvBind (FunBind _rec fun sig _ptctyps matches)
  = Set.unions [mtvVar fun, mtvTypeSig sig, mtvMatches matches]
mtvBind (PatBind _loc pat rhs) = mtvPat pat `Set.union` mtvRhs rhs

mtvTypeSig :: TypeSig Tc -> Set MetaTyVar
mtvTypeSig NoTypeSig             = Set.empty
mtvTypeSig (TypeSig _loc polyty) = mtvType polyty

mtvMatches :: [Match Tc] -> Set MetaTyVar
mtvMatches = Set.unions . map mtvMatch

mtvMatch :: Match Tc -> Set MetaTyVar
mtvMatch (Match _loc pats rhs) = mtvPats pats `Set.union` mtvRhs rhs

mtvVar :: Var Tc -> Set MetaTyVar
mtvVar = mtvType . varType

mtvCon :: TcCon Tc -> Set MetaTyVar
mtvCon = goCon . tcConCon
  where
     goCon (UserCon ucon) = mtvVar ucon
     goCon (BuiltinCon _) = Set.empty

mtvExps :: [Exp Tc] -> Set MetaTyVar
mtvExps = Set.unions . map mtvExp

mtvMaybeExp :: Maybe (Exp Tc) -> Set MetaTyVar
mtvMaybeExp = maybe Set.empty mtvExp

mtvExp :: Exp Tc -> Set MetaTyVar
mtvExp (Var x)   = mtvVar x
mtvExp (Con con) = mtvCon con
mtvExp (Lit _)   = Set.empty
mtvExp (PrefixApp op e) = mtvExp e
mtvExp (InfixApp e1 _op e2) = mtvExps [e1,e2]
mtvExp (App e1 e2) = mtvExps [e1,e2]
mtvExp (TyApp e tys) = mtvExp e `Set.union` mtvTypes tys
mtvExp (Lam _loc pats rhs)
  = mtvPats pats `Set.union` mtvRhs rhs
mtvExp (Let bs body)
  = mtvBinds bs `Set.union` mtvExp body
mtvExp (TyLam tvs body) = mtvExp body
mtvExp (Ite ptcty g t e) = mtvExps [g,t,e] `Set.union` (F.foldMap mtvType ptcty)
mtvExp (If ptcty grhss) = mtvGuardedRhss grhss `Set.union` (F.foldMap mtvType ptcty)
mtvExp (Case exp (PostTc casety) alts)
  = Set.unions [mtvExp exp, mtvType casety, mtvAlts alts]
mtvExp (Tuple ptcty es) = mtvExps es `Set.union` (F.foldMap mtvType ptcty)
mtvExp (List ptcty es) = mtvExps es `Set.union` (F.foldMap mtvType ptcty)
mtvExp (Paren e) = mtvExp e
mtvExp (LeftSection e _op) = mtvExp e
mtvExp (RightSection _op e) = mtvExp e
mtvExp (EnumFromTo e1 e2) = mtvExps [e1,e2]
mtvExp (EnumFromThenTo e1 e2 e3) = mtvExps [e1,e2,e3]
mtvExp (Coerc _loc e polyty) = mtvExp e `Set.union` mtvType polyty
mtvExp (QP qt qvars body) = mtvQVars qvars `Set.union` mtvExp body


mtvPats :: [Pat Tc] -> Set MetaTyVar
mtvPats = Set.unions . map mtvPat

mtvPat :: Pat Tc -> Set MetaTyVar
mtvPat (VarPat x) = mtvVar x
mtvPat (LitPat _) = Set.empty
mtvPat (InfixCONSPat ptcty p1 p2) = mtvPats [p1,p2] `Set.union` (F.foldMap mtvType ptcty)
mtvPat (ConPat con ptctys ps) = mtvCon con `Set.union` mtvPats ps `Set.union` (F.foldMap mtvTypes ptctys)
mtvPat (TuplePat ps ptcty) = mtvPats ps `Set.union` (F.foldMap mtvType ptcty)
mtvPat (ListPat ps ptcty) = mtvPats ps `Set.union` (F.foldMap mtvType ptcty)
mtvPat (ParenPat p) = mtvPat p
mtvPat (WildPat wild_var)     = mtvVar wild_var
mtvPat (AsPat x p)  = mtvVar x `Set.union` mtvPat p
-- mtvPat (SigPat p ty) = mtvPat p `Set.union` mtvType ty

mtvQVars :: [QVar Tc] -> Set MetaTyVar
mtvQVars = Set.unions . map mtvQVar

mtvQVar :: QVar Tc -> Set MetaTyVar
mtvQVar (QVar x mb_ty) = mtvVar x `Set.union` (F.foldMap mtvType mb_ty)

mtvAlts :: [Alt Tc] -> Set MetaTyVar
mtvAlts = Set.unions . map mtvAlt

mtvAlt :: Alt Tc -> Set MetaTyVar
mtvAlt (Alt _loc pat rhs) = mtvPat pat `Set.union` mtvRhs rhs

mtvRhs :: Rhs Tc -> Set MetaTyVar
mtvRhs (Rhs tcty grhs whr) = mtvBinds whr `Set.union` mtvGRhs grhs `Set.union` (F.foldMap mtvType tcty)

mtvGRhs :: GRhs Tc -> Set MetaTyVar
mtvGRhs (UnGuarded e)   = mtvExp e
mtvGRhs (Guarded grhss) = mtvGuardedRhss grhss

mtvGuardedRhss :: GuardedRhss Tc -> Set MetaTyVar
mtvGuardedRhss (GuardedRhss grhss elserhs)
  = Set.unions $ mtvElse elserhs : map mtvGuardedRhs grhss 

mtvGuardedRhs :: GuardedRhs Tc -> Set MetaTyVar
mtvGuardedRhs (GuardedRhs _loc g e) = mtvExps [g,e]

mtvElse :: Else Tc -> Set MetaTyVar
mtvElse NoElse        = Set.empty
mtvElse (Else _loc e) = mtvExp e

mtvTypes :: [Type c Tc] -> Set MetaTyVar
mtvTypes = Set.unions . map mtvType

mtvType :: Type c Tc -> Set MetaTyVar
mtvType (VarTy _) = Set.empty
mtvType (ConTy _ args) = mtvTypes args
mtvType (PredTy pat ty mb_prop)
  = Set.unions [mtvPat pat, mtvType ty,  mtvMaybeExp mb_prop]
mtvType (FunTy dom rang)
  = mtvDom dom `Set.union` mtvType rang
mtvType (ListTy ty) = mtvType ty
mtvType (TupleTy ds) = mtvDoms ds
mtvType (MetaTy mtv) = Set.singleton mtv
mtvType (ForallTy _tvs ty) = mtvType ty

mtvDoms :: [Dom Tc] -> Set MetaTyVar
mtvDoms = Set.unions . map mtvDom

mtvDom :: Dom Tc -> Set MetaTyVar
mtvDom (Dom Nothing ty Nothing) = mtvType ty
mtvDom (Dom (Just pat) ty mb_prop)
  = Set.unions [mtvPat pat, mtvType ty, mtvMaybeExp mb_prop]
