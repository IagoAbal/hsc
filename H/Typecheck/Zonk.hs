{-# LANGUAGE GADTs, NamedFieldPuns #-}

module H.Typecheck.Zonk where

import H.Typecheck.TcM

import H.Syntax
import H.Phase

import Control.Monad
import Control.Monad.IO.Class
import qualified Data.Traversable as T


zonkDecls :: MonadIO m => [Decl Tc] -> m [Decl Tc]
zonkDecls = mapM zonkDecl

zonkDecl :: MonadIO m => Decl Tc -> m (Decl Tc)
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

zonkConDecls :: MonadIO m => [ConDecl Tc] -> m [ConDecl Tc]
zonkConDecls = mapM zonkConDecl

zonkConDecl :: MonadIO m => ConDecl Tc -> m (ConDecl Tc)
zonkConDecl (ConDecl loc name doms)
  = liftM (ConDecl loc name) $ zonkDoms doms
zonkConDecl _other = undefined -- impossible

zonkBinds :: MonadIO m => [Bind Tc] -> m [Bind Tc]
zonkBinds = mapM zonkBind

zonkBind :: MonadIO m => Bind Tc -> m (Bind Tc)
zonkBind (FunBind rec fun sig ptctyps matches)
  = liftM4 (FunBind rec) (zonkVar fun) (zonkTypeSig sig) (return ptctyps) (zonkMatches matches)
zonkBind (PatBind loc pat rhs)
  = liftM2 (PatBind loc) (zonkPat pat) (zonkRhs rhs)

zonkTypeSig :: MonadIO m => TypeSig Tc -> m (TypeSig Tc)
zonkTypeSig NoTypeSig = return NoTypeSig
zonkTypeSig (TypeSig loc polyty)
  = liftM (TypeSig loc) $ zonkType polyty

zonkMatches :: MonadIO m => [Match Tc] -> m [Match Tc]
zonkMatches = mapM zonkMatch

zonkMatch :: MonadIO m => Match Tc -> m (Match Tc)
zonkMatch (Match loc pats rhs)
  = liftM2 (Match loc) (zonkPats pats) (zonkRhs rhs)

zonkVar :: MonadIO m => Var Tc -> m (Var Tc)
zonkVar x@V{varType} = do
  varType' <- zonkType varType
  return x{varType = varType'}

zonkCon :: MonadIO m => TcCon Tc -> m (TcCon Tc)
zonkCon con@TcCon{tcConCon} = do
  tcConCon' <- goCon tcConCon
  return con{tcConCon = tcConCon'}
  where
    goCon (UserCon ucon)      = liftM UserCon $ zonkVar ucon
    goCon bcon@(BuiltinCon _) = return bcon

zonkExps :: MonadIO m => [Exp Tc] -> m [Exp Tc]
zonkExps = mapM zonkExp

zonkExp :: MonadIO m => Exp Tc -> m (Exp Tc)
zonkExp (Var x) = liftM Var $ zonkVar x
zonkExp (Con con) = liftM Con $ zonkCon con
zonkExp op@(Op _) = return op
zonkExp e@(Lit _) = return e
zonkExp (PrefixApp op e) = liftM2 PrefixApp (zonkExp op) (zonkExp e)
zonkExp (InfixApp e1 op e2) = liftM3 InfixApp (zonkExp e1) (zonkExp op) (zonkExp e2)
zonkExp (App f a) = liftM2 App (zonkExp f) (zonkExp a)
zonkExp (TyApp expr tys) = liftM2 TyApp (zonkExp expr) (zonkTypes tys)
zonkExp (Lam loc pats body)
  = liftM2 (Lam loc) (zonkPats pats) (zonkExp body)
zonkExp (Let binds body) = liftM2 Let (zonkBinds binds) (zonkExp body)
zonkExp (TyLam tvs expr) = liftM (TyLam tvs) $ zonkExp expr
zonkExp (Ite ptcty g t e) = liftM4 Ite (T.mapM zonkType ptcty) (zonkExp g) (zonkExp t) (zonkExp e)
zonkExp (If ptcty grhss) = liftM2 If (T.mapM zonkType ptcty) (zonkGuardedRhss grhss)
zonkExp (Case scrut ptcty alts)
  = liftM3 Case (zonkExp scrut) (T.mapM zonkType ptcty) (zonkAlts alts)
zonkExp (Tuple ptcty es) = liftM2 Tuple (T.mapM zonkType ptcty) (zonkExps es)
zonkExp (List ptcty es) = liftM2 List (T.mapM zonkType ptcty) (zonkExps es)
zonkExp (Paren e) = liftM Paren $ zonkExp e
zonkExp (LeftSection e1 op) = liftM2 LeftSection (zonkExp e1) (zonkExp op)
zonkExp (RightSection op e2) = liftM2 RightSection (zonkExp op) (zonkExp e2)
zonkExp (EnumFromTo e1 en) = liftM2 EnumFromTo (zonkExp e1) (zonkExp en)
zonkExp (EnumFromThenTo e1 e2 en)
  = liftM3 EnumFromThenTo (zonkExp e1) (zonkExp e2) (zonkExp en)
zonkExp (Coerc loc expr polyty)
  = liftM2 (Coerc loc) (zonkExp expr) (zonkType polyty)
zonkExp (QP qt pats prop) = liftM2 (QP qt) (zonkPats pats) (zonkExp prop)
zonkExp _other = undefined -- impossible

zonkPats :: MonadIO m => [Pat Tc] -> m [Pat Tc]
zonkPats = mapM zonkPat

zonkPat :: MonadIO m => Pat Tc -> m (Pat Tc)
zonkPat (VarPat x) = liftM VarPat $ zonkVar x
zonkPat pat@(LitPat _) = return pat
zonkPat (InfixCONSPat ptcty p1 p2)
  = liftM3 InfixCONSPat (T.mapM zonkType ptcty) (zonkPat p1) (zonkPat p2)
zonkPat (ConPat con ptctys pats) = liftM3 ConPat (zonkCon con) (T.mapM zonkTypes ptctys) (zonkPats pats)
zonkPat (TuplePat ps ptcty) = liftM2 TuplePat (zonkPats ps) (T.mapM zonkType ptcty)
zonkPat (ListPat ps ptcty) = liftM2 ListPat (zonkPats ps) (T.mapM zonkType ptcty)
zonkPat (ParenPat p) = liftM ParenPat $ zonkPat p
zonkPat (WildPat wild_var) = liftM WildPat $ zonkVar wild_var
zonkPat (AsPat x pat) = liftM2 AsPat (zonkVar x) (zonkPat pat)
zonkPat (SigPat pat ty) = liftM2 SigPat (zonkPat pat) (zonkType ty)

zonkAlts :: MonadIO m => [Alt Tc] -> m [Alt Tc]
zonkAlts = mapM zonkAlt

zonkAlt :: MonadIO m => Alt Tc -> m (Alt Tc)
zonkAlt (Alt loc pat rhs) = liftM2 (Alt loc) (zonkPat pat) (zonkRhs rhs)

zonkRhs :: MonadIO m => Rhs Tc -> m (Rhs Tc)
zonkRhs (Rhs tcty grhs whr) = liftM3 Rhs (T.mapM zonkType tcty) (zonkGRhs grhs) (zonkBinds whr)

zonkGRhs :: MonadIO m => GRhs Tc -> m (GRhs Tc)
zonkGRhs (UnGuarded expr) = liftM UnGuarded $ zonkExp expr
zonkGRhs (Guarded grhss) = liftM Guarded $ zonkGuardedRhss grhss

zonkGuardedRhss :: MonadIO m => GuardedRhss Tc -> m (GuardedRhss Tc)
zonkGuardedRhss (GuardedRhss grhss elserhs)
  = liftM2 GuardedRhss (mapM zonkGuardedRhs grhss) (zonkElse elserhs)
zonkGuardedRhss _other = undefined -- impossible

zonkGuardedRhs :: MonadIO m => GuardedRhs Tc -> m (GuardedRhs Tc)
zonkGuardedRhs (GuardedRhs loc g e)
  = liftM2 (GuardedRhs loc) (zonkExp g) (zonkExp e)

zonkElse :: MonadIO m => Else Tc -> m (Else Tc)
zonkElse NoElse          = return NoElse
zonkElse (Else loc expr) = liftM (Else loc) $ zonkExp expr


zonkTypes :: MonadIO m => [Type c Tc] -> m [Type c Tc]
zonkTypes = mapM zonkType

zonkType :: MonadIO m => Type c Tc -> m (Type c Tc)
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
zonkType _other = undefined -- impossible

zonkDoms :: MonadIO m => [Dom Tc] -> m [Dom Tc]
zonkDoms = mapM zonkDom

zonkDom :: MonadIO m => Dom Tc -> m (Dom Tc)
zonkDom (Dom Nothing ty Nothing) = do
  ty' <- zonkType ty
  return (Dom Nothing ty' Nothing)
zonkDom (Dom (Just pat) ty mb_prop) = do
  pat' <- zonkPat pat
  ty' <- zonkType ty
  mb_prop' <- T.mapM zonkExp mb_prop
  return (Dom (Just pat') ty' mb_prop')
zonkDom _other = undefined -- impossible

---

headZonkType :: MonadIO m => Type c Tc -> m (Type c Tc)
headZonkType mty@(MetaTy mtv) = do
  mb_ty <- readMetaTyVar mtv
  case mb_ty of
      Nothing  -> return mty
      Just ty -> do
        ty' <- headZonkType ty
        writeMetaTyVar mtv ty'   -- "Short out" multiple hops
        return $ tau2type ty'
headZonkType ty = return ty
