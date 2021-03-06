{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module H.Desugar where

import Name
import Sorted

import qualified Core.Syntax as Core
import qualified Core.Syntax.Subst1.Direct as Core
import qualified Core.Prop as Core
import H.Monad
import H.Syntax
import H.SrcContext
import H.Typecheck.TCC ( TccHypoThing(..), TccPropCtxt, TCC(..), ModTCCs )
import H.Typecheck.Utils
  ( tcExprType, tcExprTau, tcRhsType, tcPatsTypes
  , instFunTy, instDoms, instSigmaType
  , instWithVars, instTupleWithVars )

import Control.Applicative ( (<$>), (<*>) )
import Control.Monad.Error
import Data.Char ( isLower )
import Data.Foldable ( toList )
import Data.List ( find, nub )
import qualified Data.IntMap as IMap
import Data.Maybe ( catMaybes )
import qualified Data.Set as Set
import qualified Data.Sequence as Seq
import qualified Data.Traversable as T

import Pretty

#include "bug.h"


type DsgM = H () () ()


dsgModule :: Module Ti -> ModTCCs -> DsgM Core.Module
dsgModule (Module _ modname decls) tccs = do
  decls' <- dsgDecls decls
  tccs' <- dsgTCCs tccs
  let goalPOs = collectGoalPOs decls'
  return $ Core.Module (dsgModuleName modname) decls' $ build_PO_map (tccs' ++ goalPOs)
  where build_PO_map = IMap.fromList . zip [1..]

-- TODO
-- Do this at other point so we can get better contextual information
-- I think I should collect this POs during Coerce phase,
collectGoalPOs :: [Core.Decl] -> [Core.ProofObligation]
collectGoalPOs [] = []
collectGoalPOs (Core.GoalDecl gtype gname _typs prop:ds) =
  Core.GoalPO (render $ pretty gname) gname gtype prop : collectGoalPOs ds
collectGoalPOs (_:ds) = collectGoalPOs ds

dsgModuleName :: ModuleName -> Core.ModuleName
dsgModuleName (ModName n) = Core.ModName n

dsgVars :: [Var Ti] -> DsgM [Core.Var]
dsgVars = mapM dsgVar

dsgVar :: Var Ti -> DsgM Core.Var
dsgVar (V x ty isSk) = do
  tyC <- dsgType ty
  return $ Core.V x tyC isSk

dsgTyVars :: [TyVar] -> [Core.TyVar]
dsgTyVars = map dsgTyVar

dsgTyVar :: TyVar -> Core.TyVar
dsgTyVar (TyV a ki isSk) = Core.TyV a (dsgKind ki) isSk

dsgDecls :: [Decl Ti] -> DsgM [Core.Decl]
dsgDecls decls = concat <$> mapM dsgDecl decls

dsgDecl :: Decl Ti -> DsgM [Core.Decl]
dsgDecl (TypeDecl _ u typs rhs) = do
  rhs_C <- dsgType rhs
  return [Core.TypeDecl (dsgTyVar u) (dsgTyVars typs) rhs_C]
dsgDecl (DataDecl _ u typs cons) = do
  cons_C <- mapM dsgConDecl cons
  return [Core.DataDecl (dsgTyVar u) (dsgTyVars typs) cons_C]
dsgDecl (ValDecl bind) = map Core.ValDecl <$> dsgBind bind
dsgDecl (GoalDecl _ gtype t typs prop) = do
  prop_C <- dsgExp prop
  return [Core.GoalDecl (dsgGoalType gtype) t (dsgTyVars typs) prop_C]


dsgConDecl :: ConDecl Ti -> DsgM Core.ConDecl
dsgConDecl (ConDecl _ con ds)
  = Core.ConDecl <$> dsgVar con <*> dsgDoms ds

dsgGoalType :: GoalType -> Core.GoalType
dsgGoalType TheoremGoal = Core.TheoremGoal
dsgGoalType LemmaGoal = Core.LemmaGoal

dsgBinds :: [Bind Ti] -> DsgM [Core.Bind]
dsgBinds binds = concat <$> mapM dsgBind binds

dsgIsRec :: IsRec Ti -> Core.IsRec
dsgIsRec Rec    = Core.Rec
dsgIsRec NonRec = Core.NonRec

dsgBind :: Bind Ti -> DsgM [Core.Bind]
dsgBind (FunBind rec fun _sig tvs matches) = do
  fun_C <- dsgVar fun
  fun_tau <- instSigmaType fun_ty (map VarTy tvs)
  let (doms,_) = splitFunTy arity fun_tau
  qs <- matches2eqs matches
  (xs,bind_rhs) <- matchEq doms qs
  let tvs_C = dsgTyVars tvs
  return [Core.FunBind (dsgIsRec rec) fun_C tvs_C xs bind_rhs]
  where fun_ty = sortOf fun
        arity = matchArity $ head matches
dsgBind (PatBind _ pat rhs) = dsgPatBind pat rhs

dsgPatBind :: Pat Ti -> Rhs Ti -> DsgM [Core.Bind]
dsgPatBind pat rhs = do
  aux <- newVarId "t" ty
  rhs_C <- dsgRhs rhs
  aux_C <- dsgVar aux
  let aux_bind = Core.mkSimpleBind aux_C rhs_C
      pb_case x = mkExpRhs (varTau x) $
                    Case (varTau x) (Var aux)
                        [Alt Nothing pat (mkVarRhs x)]
      pat_xs = Set.elems $ bsPat pat
  xs_binds <- forM pat_xs
                (\x -> Core.mkSimpleBind <$> dsgVar x <*> (dsgRhs $ pb_case x))
  return $ aux_bind:xs_binds
  where ty = tau2sigma $ tcRhsType rhs


dsgExps :: [Exp Ti] -> DsgM [Core.Exp]
dsgExps = mapM dsgExp

dsgExp :: Exp Ti -> DsgM Core.Exp
dsgExp (Var x) = Core.Var <$> dsgVar x
dsgExp (Par x) = Core.Par <$> dsgVar x
dsgExp (Con tcon) = Core.Con <$> dsgTcCon tcon
  -- polymorphic op, that is: ::, == or /=
dsgExp (TyApp (Op op) tys) = do
  let (ForallTy tvs opTy) :: Sigma Ti = typeOf op
  opTau <- subst_type [] (zip tvs tys) opTy
  tysC <- mapM dsgType tys
  ([d1,d2],res) <- Core.unFunTy <$> dsgType opTau
  let ty1 = Core.tau2sigma $ Core.dom2type d1
      ty2 = Core.tau2sigma $ Core.dom2type d2
      opExp = Core.OpExp tysC $ dsgOp op
  x <- Core.newVar "x" ty1
  y <- Core.newVar "y" ty2
  return $ Core.Lam [x,y] $ Core.mkExpRhs res $
              Core.InfixApp (Core.Var x) opExp (Core.Var y)
  -- any operator here has a tau-type
dsgExp (Op op) = do
--   let opTy :: Tau Ti = type2tau (typeOf op :: Sigma Ti)
  ([d1,d2],res) <- Core.unFunTy <$> dsgType opTy
  let ty1 = Core.tau2sigma $ Core.dom2type d1
      ty2 = Core.tau2sigma $ Core.dom2type d2
  x <- Core.newVar "x" ty1
  y <- Core.newVar "y" ty2
  return $ Core.Lam [x,y] $ Core.mkExpRhs res $
              Core.InfixApp (Core.Var x) opExp (Core.Var y)
  where opTy = type2tau (typeOf op :: Sigma Ti)
        opExp = Core.OpExp [] $ dsgOp op
dsgExp (Lit lit) = return $ Core.Lit $ dsgLit lit
dsgExp (PrefixApp (Op op) e) = do
  e_C <- dsgExp e
  let op_C = dsgOp op
  return $ Core.PrefixApp (Core.OpExp [] op_C) e_C
dsgExp (InfixApp e1 opE e2) = do
  e1_C <- dsgExp e1
  e2_C <- dsgExp e2
  opE_C <- dsgOpExp opE
  return $ Core.InfixApp e1_C opE_C e2_C
dsgExp (App e1 e2) = do
    e1_C <- dsgExp e1
    e2_C <- dsgExp e2
    return $ Core.App e1_C e2_C
dsgExp (TyApp e tys) = Core.TyApp <$> dsgExp e <*> dsgTypes tys
dsgExp (Lam _ pats rhs') = do
  pats_tys <- tcPatsTypes pats
  let doms = zipWith mkPatDom pats pats_tys
  q <- mkEq pats rhs'
  (xs,rhs) <- matchEq doms [q]
  return $ Core.Lam xs rhs
dsgExp (Let binds body) = Core.mkLet <$> dsgBinds binds <*> dsgExp body
dsgExp (TyLam tvs e) = Core.TyLam tvs_C <$> dsgExp e
  where tvs_C = dsgTyVars tvs
dsgExp (Ite ty g e t)
  = Core.Ite <$> dsgType ty <*> dsgExp g <*> dsgExp e <*> dsgExp t
dsgExp (If ty grhss)
  = Core.If <$> dsgType ty <*> dsgGuardedRhss grhss
dsgExp (Case _ty scrut alts) = do
  qs <- mapM alt2eq alts
  matchCase scrut qs
dsgExp (Tuple ty es) = Core.Tuple <$> dsgType ty <*> dsgExps es
dsgExp (List ty es) = Core.List <$> dsgType ty <*> dsgExps es
dsgExp (Paren e) = Core.Paren <$> dsgExp e
dsgExp (LeftSection e1 opE) = do
  e1_C <- dsgExp e1
  opE_C <- dsgOpExp opE
  app_ty <- tcExprType $ App opE e1
    -- FIXME: A proper "matchFunTy" considering type synonyms as well...
  let FunTy d r = mu_0 $ type2tau app_ty
  y' <- newVarId "y" (dom2type d)
  r' <- instFunTy (d,r) (Var y')
  y <- dsgVar y'
  rhs_ty <- dsgType r'
  return $ Core.Lam [y] $ Core.Rhs rhs_ty $ Core.InfixApp e1_C opE_C (Core.Var y)
dsgExp (RightSection opE e2) = do
  op_ty <- tcExprTau opE
  opE_C <- dsgOpExp opE
  e2_C <- dsgExp e2
  let FunTy d1 r1 = mu_0 op_ty
  x' <- newVarId "x" (dom2type d1)
  r1' <- instFunTy (d1,r1) (Var x')
  let FunTy d2 r = mu_0 r1'
  r' <- instFunTy (d2,r) e2
  x <- dsgVar x'
  rhs_ty <- dsgType r'
  return $ Core.Lam [x] $ Core.Rhs rhs_ty $ Core.InfixApp (Core.Var x) opE_C e2_C
dsgExp (EnumFromTo e1 e2) = Core.EnumFromTo <$> dsgExp e1 <*> dsgExp e2
dsgExp (EnumFromThenTo e1 e2 e3)
  = Core.EnumFromThenTo <$> dsgExp e1 <*> dsgExp e2 <*> dsgExp e3
dsgExp (Coerc _ e ty) = Core.Coerc <$> dsgExp e <*> dsgType ty
dsgExp (CaseP def e pat prop) = do
  e' <- dsgExp e
  (pat',pat_s) <- dsgPat pat
  prop_p <- subst_exp pat_s [] prop
  prop' <- dsgExp prop_p
  return $ Core.CaseP def e' pat' prop'
dsgExp (QP qt qvars prop)
  = Core.QP (dsgQuantifier qt) <$> dsgQVars qvars <*> dsgExp prop
dsgExp _other = impossible


dsgOpExp :: OpExp Ti -> DsgM Core.OpExp
dsgOpExp (Op op) = return $ Core.OpExp [] $ dsgOp op
dsgOpExp (TyApp (Op op) tys) = do
  tys_C <- mapM dsgType tys
  let op_C = dsgOp op
  return $ Core.OpExp tys_C op_C
dsgOpExp other = traceDoc (text "dsgOpExp other=" <> pretty other) $ undefined

dsgLit :: Lit -> Core.Lit
dsgLit (IntLit n) = Core.IntLit n

dsgBuiltinCon :: BuiltinCon -> Core.BuiltinCon
dsgBuiltinCon UnitCon = Core.UnitCon
dsgBuiltinCon FalseCon = Core.FalseCon
dsgBuiltinCon TrueCon = Core.TrueCon
dsgBuiltinCon NilCon = Core.NilCon
dsgBuiltinCon ConsCon = Core.ConsCon

dsgCon :: Con Ti -> DsgM Core.Con
dsgCon (UserCon x) = Core.UserCon <$> dsgVar x
dsgCon (BuiltinCon bcon) = return $ Core.BuiltinCon $ dsgBuiltinCon bcon

dsgTcCon :: TcCon Ti -> DsgM Core.Con
dsgTcCon = dsgCon . tcConCon

dsgOp :: Op -> Core.Op
dsgOp (BoolOp bop) = Core.BoolOp $ dsgBoolOp bop
dsgOp (IntOp iop) = Core.IntOp $ dsgIntOp iop
dsgOp CONSOp = Core.CONSOp

dsgBoolOp :: BoolOp -> Core.BoolOp
dsgBoolOp NotB = Core.NotB
dsgBoolOp OrB = Core.OrB
dsgBoolOp AndB = Core.AndB
dsgBoolOp ImpB = Core.ImpB
dsgBoolOp IffB = Core.IffB
dsgBoolOp EqB = Core.EqB
dsgBoolOp NeqB = Core.NeqB
dsgBoolOp LtB = Core.LtB
dsgBoolOp LeB = Core.LeB
dsgBoolOp GtB = Core.GtB
dsgBoolOp GeB = Core.GeB

dsgIntOp :: IntOp -> Core.IntOp
dsgIntOp NegI = Core.NegI
dsgIntOp AddI = Core.AddI
dsgIntOp SubI = Core.SubI
dsgIntOp MulI = Core.MulI
dsgIntOp DivI = Core.DivI
dsgIntOp ModI = Core.ModI
dsgIntOp ExpI = Core.ExpI

dsgQuantifier :: Quantifier -> Core.Quantifier
dsgQuantifier ExistsQ = Core.ExistsQ
dsgQuantifier ForallQ = Core.ForallQ

dsgQVar :: QVar Ti -> DsgM Core.Var
dsgQVar (QVar x _) = dsgVar x

dsgQVars :: [QVar Ti] -> DsgM [Core.Var]
dsgQVars = mapM dsgQVar

dsgPats :: [Pat Ti] -> DsgM ([Core.Pat],[(Var Ti,Exp Ti)])
dsgPats pats = do
  (pats_C,pats_ss) <- unzip <$> mapM dsgPat pats
  return (pats_C,concat pats_ss)

dsgPat :: Pat Ti -> DsgM (Core.Pat,[(Var Ti,Exp Ti)])
dsgPat (VarPat x) = do
  x_C <- dsgVar x
  return (Core.VarPat x_C,[])
dsgPat (LitPat lit) = return (Core.LitPat $ dsgLit lit,[])
dsgPat (InfixCONSPat ty p1 p2) = do
  ty_C <- dsgType ty
  (p1_C,s1) <- dsgPat p1
  (p2_C,s2) <- dsgPat p2
  return (Core.mkCONSPat ty_C p1_C p2_C,s1++s2)
dsgPat (ConPat tys tcon ps) = do
  con_C <- dsgTcCon tcon
  tys_C <- dsgTypes tys
  (ps_C,s) <- dsgPats ps
  return (Core.ConPat tys_C con_C ps_C,s)
dsgPat (TuplePat tupty ps) = do
  tupty_C <- dsgType tupty
  (ps_C,s) <- dsgPats ps
  return (Core.TuplePat tupty_C ps_C,s)
dsgPat (ListPat listty ps) = do
  let ListTy elemty = mu_0 listty
  elemty_C <- dsgType elemty
  (ps_C,s) <- dsgPats ps
  let nil  = Core.mkNILPat elemty_C
      cons = Core.mkCONSPat elemty_C
  return (foldr cons nil ps_C,s)
dsgPat (ParenPat p) = do
  (p_C,s) <- dsgPat p
  return (Core.ParenPat p_C,s)
dsgPat (WildPat x) = do
  x_C <- dsgVar x
  return (Core.VarPat x_C,[])
dsgPat (AsPat x p) = do
--   x_C <- dsgVar x
  (p_C,s) <- dsgPat p
--   return (p_C,(x_C,Core.pat2exp p_C):s)
  return (p_C,(x,pat2exp p):s)

dsgRhs :: Rhs Ti -> DsgM Core.Rhs
dsgRhs (Rhs rhs_ty' grhs whr) = do
  rhs_ty <- dsgType rhs_ty'
  binds <- dsgBinds whr
  body <- dsgGRhs rhs_ty' grhs
  return $ Core.Rhs rhs_ty $ Core.mkLet binds body

dsgGRhs :: Tau Ti -> GRhs Ti -> DsgM Core.Exp
dsgGRhs _tau (UnGuarded e)   = dsgExp e
dsgGRhs  tau (Guarded grhss)
  = Core.If <$> dsgType tau <*> dsgGuardedRhss grhss

dsgGuardedRhss :: GuardedRhss Ti -> DsgM Core.GuardedRhss
dsgGuardedRhss (GuardedRhss rhss else_rhs)
  = Core.GuardedRhss <$> mapM dsgGuardedRhs rhss <*> dsgElse else_rhs

dsgGuardedRhs :: GuardedRhs Ti -> DsgM Core.GuardedRhs
dsgGuardedRhs (GuardedRhs _ guard expr)
  = Core.GuardedRhs <$> dsgExp guard <*> dsgExp expr

dsgElse :: Else Ti -> DsgM (Maybe Core.Exp)
dsgElse NoElse     = return Nothing
dsgElse (Else _ e) = Just <$> dsgExp e


dsgTyName :: TyName Ti -> Core.TyName
dsgTyName (UserTyCon tc) = Core.UserTyCon $ dsgTyVar tc
dsgTyName (BuiltinTyCon btc) = Core.BuiltinTyCon $ dsgBuiltinTyCon btc

dsgBuiltinTyCon :: BuiltinTyCon -> Core.BuiltinTyCon
dsgBuiltinTyCon UnitTyCon = Core.UnitTyCon
dsgBuiltinTyCon BoolTyCon = Core.BoolTyCon
dsgBuiltinTyCon IntTyCon = Core.IntTyCon
dsgBuiltinTyCon NatTyCon = Core.NatTyCon
dsgBuiltinTyCon ListTyCon = Core.ListTyCon

dsgTyCon :: TyCon Ti -> DsgM Core.TyCon
dsgTyCon (AlgTyCon tyname _) = return $ Core.AlgTyCon $ dsgTyName tyname
dsgTyCon (SynTyCon tynm typs tyrhs _us)
  = Core.SynTyCon (dsgTyName tynm) (dsgTyVars typs) <$> dsgType tyrhs

dsgTypes :: [Type c Ti] -> DsgM [Core.Type c]
dsgTypes = mapM dsgType

dsgType :: Type c Ti -> DsgM (Core.Type c)
dsgType (VarTy a) = return $ Core.VarTy $ dsgTyVar a
dsgType (ConTy con tys) = Core.ConTy <$> dsgTyCon con <*> dsgTypes tys
dsgType (PredTy pat' ty' mb_prop'') = do
  ty <- dsgType ty'
  (pat,pat_s) <- dsgPat pat'
  mb_prop' <- subst_mbExp pat_s [] mb_prop''
  mb_prop <- T.mapM dsgExp mb_prop'
  return $ Core.PredTy pat ty mb_prop
dsgType (FunTy d' r'') = do
  (d,d_s) <- dsgDom d'
  r' <- subst_type d_s [] r''
  r <- dsgType r'
  return $ Core.FunTy d r
dsgType (ListTy elem_ty) = Core.ListTy <$> dsgType elem_ty
dsgType (TupleTy ds) = Core.TupleTy <$> dsgDoms ds
dsgType (ForallTy tvs ty)
  = Core.ForallTy (dsgTyVars tvs) <$> dsgType ty
dsgType _other = impossible

dsgDoms :: [Dom Ti] -> DsgM [Core.Dom]
dsgDoms [] = return []
dsgDoms (d':ds'') = do
  (d,d_s) <- dsgDom d'
  ds' <- subst_doms d_s [] ds''
  ds <- dsgDoms ds'
  return (d:ds)

dsgDom :: Dom Ti -> DsgM (Core.Dom,[(Var Ti,Exp Ti)])
dsgDom (Dom Nothing ty' Nothing) = do
  ty <- dsgType ty'
  return (Core.Dom Nothing ty Nothing,[])
dsgDom (Dom (Just pat') ty' mb_prop'') = do
  ty <- dsgType ty'
  (pat,pat_s) <- dsgPat pat'
  mb_prop' <- subst_mbExp pat_s [] mb_prop''
  mb_prop <- T.mapM dsgExp mb_prop'
  return (Core.Dom (Just pat) ty mb_prop,pat_s)
dsgDom _other = impossible

dsgKind :: Kind -> Core.Kind
dsgKind TypeKi = Core.TypeKi
dsgKind (FunKi k1 k2) = Core.FunKi (dsgKind k1) (dsgKind k2)


dsgTccHypoThing :: TccHypoThing -> DsgM Core.TccHypoThing
dsgTccHypoThing (ForAll qvs) = Core.ForAll <$> dsgQVars qvs
dsgTccHypoThing (LetIn binds) = Core.LetIn <$> dsgBinds binds
dsgTccHypoThing (Matching e pat)
    -- liftM fst is safe because pat is a simple-pat
  = Core.Matching <$> dsgExp e <*> (liftM fst $ dsgPat pat)
dsgTccHypoThing (Facts ps) = Core.Facts <$> dsgExps ps

dsgTccPropCtxt :: TccPropCtxt -> DsgM Core.TccPropCtxt
dsgTccPropCtxt ctxt = Seq.fromList <$> (mapM dsgTccHypoThing $ toList ctxt)

dsgTCC :: TCC -> DsgM Core.TCC
dsgTCC (CoercionTCC srcCtxt propCtxt expr act_ty exp_ty prop) = do
  ctxt' <- dsgTccPropCtxt propCtxt
  expr' <- dsgExp expr
  act_ty' <- dsgType act_ty
  exp_ty' <- dsgType exp_ty
  prop' <- dsgExp prop
  let tcc_PO = Core.mkTccPO ctxt' prop'
  traceDoc (text "dsgTCC prop'=" <+> pretty prop') $ do
  traceDoc (text "dsgTCC tcc_PO=" <+> pretty tcc_PO) $ do
  return $ Core.CoercionTCC (render srcCtxt)
              ctxt'
              expr' act_ty' exp_ty'
              prop' tcc_PO
--   = Core.CoercionTCC (render srcCtxt)
--       <$> dsgTccPropCtxt propCtxt
--       <*> dsgExp expr <*> dsgType act_ty <*> dsgType exp_ty
--       <*> dsgExp prop
dsgTCC (CompletenessTCC srcCtxt propCtxt prop) = do
  ctxt' <- dsgTccPropCtxt propCtxt
  prop' <- dsgExp prop
  return $ Core.CompletenessTCC (render srcCtxt)
              ctxt'
              prop'
              (Core.mkTccPO ctxt' prop')
--   = Core.CompletenessTCC (render srcCtxt)
--       <$> dsgTccPropCtxt propCtxt
--       <*> dsgExp prop

filterTCC :: Core.TCC -> DsgM (Maybe Core.TCC)
filterTCC tcc@(Core.CoercionTCC srcCtxt _ expr act_ty exp_ty _ tcc_PO)
  | act_ty == exp_ty
  = return Nothing
  | Just True <- Core.prop2bool tcc_PO
  = return Nothing
  | Just False <- Core.prop2bool tcc_PO
  = inContext (text srcCtxt) $ throwError $
      text "Coercion proved impossible:"
      $$ nest 2 (text "expression:" <+> pretty expr)
      $$ nest 2 (text "inferred type:" <+> pretty act_ty)
      $$ nest 2 (text "expected type:" <+> pretty exp_ty)
  | otherwise = return $ Just tcc
filterTCC tcc@(Core.CompletenessTCC srcCtxt _ _ tcc_PO)
  | Just True <- Core.prop2bool tcc_PO
  = return Nothing
  | Just False <- Core.prop2bool tcc_PO
  = inContext (text srcCtxt) $ throwError $
      text "Completeness violated."
  | otherwise = return $ Just tcc

dsgTCCs :: [TCC] -> DsgM [Core.TCC]
dsgTCCs tccs = catMaybes <$> mapM (dsgTCC >=> filterTCC) tccs

-- * Equations

data Equation
  = E {
    eqPats :: [SimplePat Ti]
  , eqRhs  :: Core.Rhs
  }

eqsType :: [Equation] -> Core.Tau
eqsType (E _ (Core.Rhs ty _):_) = ty
eqsType _other             = impossible

mkEq :: [Pat Ti] -> Rhs Ti -> DsgM Equation
mkEq pats rhs'' = do
  rhs' <- subst_rhs var_s [] rhs''
  rhs <- dsgRhs rhs'
  return $ E pats' rhs
  where (pats',var_s) = simplifyPats pats

alt2eq :: Alt Ti -> DsgM Equation
alt2eq (Alt _ pat rhs) = mkEq [pat] rhs

match2eq :: Match Ti -> DsgM Equation
match2eq (Match _ pats rhs) = mkEq pats rhs

matches2eqs :: [Match Ti] -> DsgM [Equation]
matches2eqs = mapM match2eq

isVar :: Equation -> Bool
isVar (E (VarPat _:_) _) = True
isVar _other             = False

isLit :: Equation -> Bool
isLit (E (LitPat _:_) _) = True
isLit _other             = False

getLit :: Equation -> Lit
getLit (E (LitPat lit:_) _) = lit
getLit _other               = bug "getLit: not a lit-pattern"

isTuple :: Equation -> Bool
isTuple (E (TuplePat _ _:_) _) = True
isTuple _other                 = False

isCon :: Equation -> Bool
isCon (E (ConPat _ _ _:_) _) = True
isCon _other                 = False

getCon :: Equation -> TcCon Ti
getCon (E (ConPat _ con _:_) _) = con
getCon _other                   = bug "getCon: not a con-pattern"

getEqPat :: Int -> Equation -> SimplePat Ti
getEqPat n (E pats _) = pats !! n

matchCase :: Exp Ti -> [Equation] -> DsgM Core.Exp
matchCase scrut qs = do
  scrut_C <- dsgExp scrut
  Core.Rhs _ e <- match_eq [scrut_C] qs
  return e

matchEq :: [Dom Ti] -> [Equation] -> DsgM ([Core.Var],Core.Rhs)
matchEq ds qs = do
  xs' <- pick_variables
  xs <- dsgVars xs'
  rhs <- match_eq (map Core.Var xs) qs
  return (xs,rhs)
  where pick_variables = go 0 [] ds
          where go _i vs_rev []     = return $ reverse vs_rev
                go  i vs_rev (d:ds) = do
                  let n = case getNameForPats (map (getEqPat i) qs) of
                              Nothing -> "x" ++ show i
                              Just n1 -> n1
                  v <- newVarId n (dom2type d)
                  ds' <- instDoms (Var v) d ds
                  go (i+1) (v:vs_rev) ds'

match_eq :: [Core.Exp] -> [Equation] -> DsgM Core.Rhs
match_eq [] []         = error "match_eq implicit default 1"
match_eq [] [E [] rhs] = return rhs
match_eq [] (_:_)      = bug "this case should be caught during typechecking"
match_eq _xs []        = error "match_eq implicit default 2"
match_eq (x:xs) qs
  | all isVar   qs = matchVar x xs qs
  | all isLit   qs = matchLit x xs qs
  | all isTuple qs = matchTuple x xs qs
  | all isCon   qs = matchCon x xs qs
  | otherwise = bug "this case should be caught during typechecking"


-- I don't have to apply the substitution inside 'pats' because
-- all those variables will be replaced by fresh ones that have the
-- right types.
subst_eq :: Var Ti -> Core.Exp -> Equation -> DsgM Equation
subst_eq y' x (E pats rhs) = do
  y <- dsgVar y'
  let rhs' = Core.substRhs [(y,x)] [] rhs
  return (E pats rhs')

getNameForPats :: [Pat Ti] -> Maybe String
getNameForPats pats = do
  VarPat var <- find is_ok_varpat pats
  return $ clean_str var
  where clean_str = dropWhile (== '_') . occString . occNameOf
        is_ok_varpat (VarPat x) = isLower $ head $ clean_str x
        is_ok_varpat _other     = False


matchVar :: Core.Exp -> [Core.Exp] -> [Equation] -> DsgM Core.Rhs
matchVar x xs qs = do
  qs' <- sequence [ subst_eq y x q'
                  | E (VarPat y:ps) rhs <- qs
                  , let q' = E ps rhs
                  ]
  match_eq xs qs'

matchLit :: Core.Exp -> [Core.Exp] -> [Equation] -> DsgM Core.Rhs
matchLit x xs qs = do
  alts <- sequence [ matchLitClause lit xs (chooseLit lit qs) | lit <- lits ]
  let rhs_ty = eqsType qs
      rhs_exp = Core.Case rhs_ty x alts
      rhs = Core.mkExpRhs rhs_ty rhs_exp
  return rhs
  where lits = nub $ map getLit qs

chooseLit :: Lit -> [Equation] -> [Equation]
chooseLit lit qs = [q | q <- qs, getLit q == lit]

matchLitClause :: Lit -> [Core.Exp] -> [Equation] -> DsgM Core.Alt
matchLitClause lit' xs qs = do
  let lit = dsgLit lit'
  alt_rhs <- match_eq xs [ E ps rhs | E (LitPat _:ps) rhs <- qs]
  return $ Core.Alt (Core.LitPat lit) alt_rhs

matchTuple :: Core.Exp -> [Core.Exp] -> [Equation] -> DsgM Core.Rhs
matchTuple x xs qs = do
  let E (TuplePat tup_ty' _:_) _ = head qs
      TupleTy ds = mu_0 tup_ty'
  tup_ty <- dsgType tup_ty'
  (_,ys') <- instTupleWithVars ds
  ys <- dsgVars ys'
  let vs = map Core.Var ys
  alt_rhs <- match_eq (vs++xs) [E (ps1++ps) rhs | E (TuplePat _ ps1:ps) rhs <- qs]
  let alts = [Core.Alt (Core.TuplePat tup_ty (map Core.VarPat ys)) alt_rhs]
      rhs_ty = eqsType qs
      rhs_exp = Core.Case rhs_ty x alts
      rhs = Core.mkExpRhs rhs_ty rhs_exp
  return rhs

matchCon :: Core.Exp -> [Core.Exp] -> [Equation] -> DsgM Core.Rhs
matchCon x xs qs = do
  alts <- sequence [ matchClause c xs (choose c qs) | c <- cs ]
  let rhs_ty = eqsType qs
      rhs_exp = Core.Case rhs_ty x alts
      rhs = Core.mkExpRhs rhs_ty rhs_exp
  return rhs
  where cs = nub $ map getCon qs

matchClause :: TcCon Ti -> [Core.Exp] -> [Equation] -> DsgM Core.Alt
matchClause con' xs qs = do
  let E (ConPat typs' _ _:_) _ = head qs
  (_,ys') <- instWithVars (sortOf con') typs' (Con con')
  con <- dsgTcCon con'
  typs <- dsgTypes typs'
  ys <- dsgVars ys'
  let vs = map Core.Var ys
  alt_rhs <- match_eq (vs++xs) [E (ps1++ps) rhs | E (ConPat _ _ ps1:ps) rhs <- qs]
  return $ Core.Alt (Core.ConPat typs con (map Core.VarPat ys)) alt_rhs

choose :: TcCon Ti -> [Equation] -> [Equation]
choose c qs = [q | q <- qs, getCon q == c]
