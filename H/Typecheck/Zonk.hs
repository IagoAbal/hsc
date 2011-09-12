{-# LANGUAGE GADTs, NamedFieldPuns #-}

module H.Typecheck.Zonk where

import H.Typecheck.TcM

import H.Syntax
import H.Phase
import H.Pretty

import Control.Monad
import qualified Data.Traversable as T


zonkDecls :: [Decl Tc] -> TcM [Decl Tc]
zonkDecls = mapM zonkDecl

zonkDecl :: Decl Tc -> TcM (Decl Tc)
-- TypeDecl ::	SrcLoc -> UTyNAME p -> TyParams p -> Type p -> Decl p
zonkDecl (TypeDecl loc ty_name ty_params ty_rhs)
  = liftM (TypeDecl loc ty_name ty_params) $ zonkType ty_rhs
-- DataDecl ::	SrcLoc -> UTyNAME p -> TyParams p -> [ConDecl p] -> Decl p
zonkDecl (DataDecl loc data_name data_params constrs)
  = liftM (DataDecl loc data_name data_params) $ zonkConDecls constrs
zonkDecl (ValDecl bind) = liftM ValDecl $ zonkBind bind
-- GoalDecl :: SrcLoc -> GoalType -> GoalNAME p -> PostTcTyParams p -> Prop p -> Decl p
zonkDecl (GoalDecl loc gtype gname pctyps prop)
  = liftM (GoalDecl loc gtype gname pctyps) $ zonkExp prop

zonkConDecls :: [ConDecl Tc] -> TcM [ConDecl Tc]
zonkConDecls = mapM zonkConDecl

zonkConDecl :: ConDecl Tc -> TcM (ConDecl Tc)
zonkConDecl (ConDecl loc name doms)
  = liftM (ConDecl loc name) $ zonkDoms doms

zonkBinds :: [Bind Tc] -> TcM [Bind Tc]
zonkBinds = mapM zonkBind

zonkBind :: Bind Tc -> TcM (Bind Tc)
zonkBind (FunBind rec fun sig ptctyps matches)
  = liftM4 (FunBind rec) (zonkVar fun) (zonkTypeSig sig) (return ptctyps) (zonkMatches matches)
zonkBind (PatBind loc pat rhs)
  = liftM2 (PatBind loc) (zonkPat pat) (zonkRhs rhs)

zonkTypeSig :: TypeSig Tc -> TcM (TypeSig Tc)
zonkTypeSig NoTypeSig = return NoTypeSig
zonkTypeSig (TypeSig loc polyty)
  = liftM (TypeSig loc) $ zonkType polyty

zonkMatches :: [Match Tc] -> TcM [Match Tc]
zonkMatches = mapM zonkMatch

zonkMatch :: Match Tc -> TcM (Match Tc)
zonkMatch (Match loc pats rhs)
  = liftM2 (Match loc) (zonkPats pats) (zonkRhs rhs)

zonkVar :: Var Tc -> TcM (Var Tc)
zonkVar x@V{varType} = do
  varType' <- zonkType varType
  return x{varType = varType'}

zonkCon :: Con Tc -> TcM (Con Tc)
zonkCon (UserCon ucon)      = liftM UserCon $ zonkVar ucon
zonkCon bcon@(BuiltinCon _) = return bcon

zonkExps :: [Exp Tc] -> TcM [Exp Tc]
zonkExps = mapM zonkExp

zonkExp :: Exp Tc -> TcM (Exp Tc)
zonkExp (Var x) = liftM Var $ zonkVar x
zonkExp (Con con) = liftM Con $ zonkCon con
zonkExp op@(Op _) = return op
zonkExp exp@(Lit _) = return exp
zonkExp (PrefixApp op e) = liftM2 PrefixApp (zonkExp op) (zonkExp e)
zonkExp (InfixApp e1 op e2) = liftM3 InfixApp (zonkExp e1) (zonkExp op) (zonkExp e2)
zonkExp (App f a) = liftM2 App (zonkExp f) (zonkExp a)
zonkExp (TyApp exp tys) = liftM2 TyApp (zonkExp exp) (zonkTypes tys)
zonkExp (Lam loc pats body)
  = liftM2 (Lam loc) (zonkPats pats) (zonkExp body)
zonkExp (Let binds exp) = liftM2 Let (zonkBinds binds) (zonkExp exp)
zonkExp (TyLam tvs exp) = liftM (TyLam tvs) $ zonkExp exp
zonkExp (Ite g t e) = liftM3 Ite (zonkExp g) (zonkExp t) (zonkExp e)
zonkExp (If grhss) = liftM If $ zonkGuardedRhss grhss
zonkExp (Case exp ptcty alts)
  = liftM3 Case (zonkExp exp) (T.mapM zonkType ptcty) (zonkAlts alts)
zonkExp (Tuple ptcty es) = liftM2 Tuple (T.mapM zonkType ptcty) (zonkExps es)
zonkExp (List ptcty es) = liftM2 List (T.mapM zonkType ptcty) (zonkExps es)
zonkExp (Paren e) = liftM Paren $ zonkExp e
zonkExp (LeftSection e1 op) = liftM2 LeftSection (zonkExp e1) (zonkExp op)
zonkExp (RightSection op e2) = liftM2 RightSection (zonkExp op) (zonkExp e2)
zonkExp (EnumFromTo e1 en) = liftM2 EnumFromTo (zonkExp e1) (zonkExp en)
zonkExp (EnumFromThenTo e1 e2 en)
  = liftM3 EnumFromThenTo (zonkExp e1) (zonkExp e2) (zonkExp en)
zonkExp (Coerc loc exp polyty)
  = liftM2 (Coerc loc) (zonkExp exp) (zonkType polyty)
zonkExp (QP qt pats prop) = liftM2 (QP qt) (zonkPats pats) (zonkExp prop)

zonkPats :: [Pat Tc] -> TcM [Pat Tc]
zonkPats = mapM zonkPat

zonkPat :: Pat Tc -> TcM (Pat Tc)
zonkPat (VarPat x) = liftM VarPat $ zonkVar x
zonkPat pat@(LitPat _) = return pat
zonkPat (InfixPat p1 bcon ptctys p2)
  = liftM3 (flip InfixPat bcon) (zonkPat p1) (T.mapM zonkTypes ptctys) (zonkPat p2)
zonkPat (ConPat con ptctys pats) = liftM3 ConPat (zonkCon con) (T.mapM zonkTypes ptctys) (zonkPats pats)
zonkPat (TuplePat ps ptcty) = liftM2 TuplePat (zonkPats ps) (T.mapM zonkType ptcty)
zonkPat (ListPat ps ptcty) = liftM2 ListPat (zonkPats ps) (T.mapM zonkType ptcty)
zonkPat (ParenPat p) = liftM ParenPat $ zonkPat p
zonkPat (WildPat ptcty) = liftM WildPat (T.mapM zonkType ptcty)
zonkPat (AsPat x pat) = liftM2 AsPat (zonkVar x) (zonkPat pat)
zonkPat (SigPat pat ty) = liftM2 SigPat (zonkPat pat) (zonkType ty)

zonkAlts :: [Alt Tc] -> TcM [Alt Tc]
zonkAlts = mapM zonkAlt

zonkAlt :: Alt Tc -> TcM (Alt Tc)
zonkAlt (Alt loc pat rhs) = liftM2 (Alt loc) (zonkPat pat) (zonkRhs rhs)

zonkRhs :: Rhs Tc -> TcM (Rhs Tc)
zonkRhs (Rhs grhs whr) = liftM2 Rhs (zonkGRhs grhs) (zonkBinds whr)

zonkGRhs :: GRhs Tc -> TcM (GRhs Tc)
zonkGRhs (UnGuarded exp) = liftM UnGuarded $ zonkExp exp
zonkGRhs (Guarded grhss) = liftM Guarded $ zonkGuardedRhss grhss

zonkGuardedRhss :: GuardedRhss Tc -> TcM (GuardedRhss Tc)
zonkGuardedRhss (GuardedRhss grhss elserhs)
  = liftM2 GuardedRhss (mapM zonkGuardedRhs grhss) (zonkElse elserhs)

zonkGuardedRhs :: GuardedRhs Tc -> TcM (GuardedRhs Tc)
zonkGuardedRhs (GuardedRhs loc g e)
  = liftM2 (GuardedRhs loc) (zonkExp g) (zonkExp e)

zonkElse :: Else Tc -> TcM (Else Tc)
zonkElse NoElse = return NoElse
zonkElse (Else loc exp) = liftM (Else loc) $ zonkExp exp


zonkTypes :: [Type c Tc] -> TcM [Type c Tc]
zonkTypes = mapM zonkType

zonkType :: Type c Tc -> TcM (Type c Tc)
zonkType ty@(VarTy _) = return ty
  -- ?? there is no need to go into the type constructor ...
zonkType (ConTy tc args) = liftM (ConTy tc) $ zonkTypes args
zonkType (PredTy pat ty mbprop)
  = liftM3 PredTy (zonkPat pat) (zonkType ty) (T.mapM zonkExp mbprop)
zonkType (FunTy dom rang) = liftM2 FunTy (zonkDom dom) (zonkType rang)
zonkType (ListTy ty) = liftM ListTy $ zonkType ty
zonkType (TupleTy ds) = liftM TupleTy $ zonkDoms ds
zonkType mty@(MetaTy mtv) = do -- traceDoc (text "zonkType-MetaTy mty=" <+> pretty mty) $ do
  mb_ty <- readMetaTyVar mtv
  case mb_ty of
      Nothing  -> return mty
      Just ty -> do
        ty' <- zonkType ty
        writeMetaTyVar mtv ty'   -- "Short out" multiple hops
        return $ tau2type ty'
zonkType (ForallTy tvs ty) = liftM (ForallTy tvs) $ zonkType ty

zonkDoms :: [Dom Tc] -> TcM [Dom Tc]
zonkDoms = mapM zonkDom

zonkDom :: Dom Tc -> TcM (Dom Tc)
zonkDom (Dom Nothing ty Nothing) = do
  ty' <- zonkType ty
  return (Dom Nothing ty' Nothing)
zonkDom (Dom (Just pat) ty mb_prop) = do
  pat' <- zonkPat pat
  ty' <- zonkType ty
  mb_prop' <- T.mapM zonkExp mb_prop
  return (Dom (Just pat') ty' mb_prop')


---

headZonkType :: Type c Tc -> TcM (Type c Tc)
headZonkType mty@(MetaTy mtv) = do
  mb_ty <- readMetaTyVar mtv
  case mb_ty of
      Nothing  -> return mty
      Just ty -> do
        ty' <- headZonkType ty
        writeMetaTyVar mtv ty'   -- "Short out" multiple hops
        return $ tau2type ty'
headZonkType ty = return ty
