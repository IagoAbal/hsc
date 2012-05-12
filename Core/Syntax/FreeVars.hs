module Core.Syntax.FreeVars where


import Core.Syntax.AST

import Data.Set ( Set )
import qualified Data.Set as Set



fvBndrs :: [Var] -> Set Var
fvBndrs = Set.unions . map fvBndr

fvBndr :: Var -> Set Var
fvBndr (V _ ty _) = fvType ty

fvBinds :: [Bind] -> Set Var
fvBinds = Set.unions . map fvBind

fvBind :: Bind -> Set Var
fvBind (FunBind _rec fun _typs args rhs)
  = fvBndr fun `Set.union` (Set.delete fun $ fvRhs rhs Set.\\ Set.fromList args)
-- fvBind (PatBind pat rhs) = fvPat pat `Set.union` (fvRhs rhs Set.\\ bsPat pat)

bsBinds :: [Bind] -> Set Var
bsBinds = Set.unions . map bsBind

bsBind :: Bind -> Set Var
bsBind (FunBind _rec fun _typs _args _rhs) = Set.singleton fun
-- bsBind (PatBind pat _rhs)                  = bsPat pat

fvExps :: [Exp] -> Set Var
fvExps = Set.unions . map fvExp

fvMaybeExp :: Maybe Exp -> Set Var
fvMaybeExp = maybe Set.empty fvExp

fvExp :: Exp -> Set Var
fvExp (Var x)   = Set.singleton x
fvExp (Con _)   = Set.empty          -- ?
fvExp (Lit _)   = Set.empty
-- fvExp Undefined = Set.empty
fvExp (PrefixApp _op e) = fvExp e
fvExp (InfixApp e1 _op e2) = fvExps [e1,e2]
fvExp (App e1 e2) = fvExps [e1,e2]
fvExp (TyApp e tys) = fvExp e `Set.union` fvTypes tys
fvExp (Lam args rhs)
  = fvBndrs args `Set.union` (fvRhs rhs Set.\\ Set.fromList args)
fvExp (Let bs body)
  = fvBinds bs `Set.union` (fvExp body Set.\\ bsBinds bs)
fvExp (TyLam _tvs body) = fvExp body
fvExp (Ite _ g t e) = fvExps [g,t,e]
fvExp (If _ grhss) = fvGuardedRhss grhss
fvExp (Case ty e alts) = fvExp e `Set.union` fvType ty `Set.union` fvAlts alts
fvExp (Tuple _ es) = fvExps es
fvExp (List _ es) = fvExps es
fvExp (Paren e) = fvExp e
fvExp (EnumFromTo e1 e2) = fvExps [e1,e2]
fvExp (EnumFromThenTo e1 e2 e3) = fvExps [e1,e2,e3]
fvExp (Coerc e ty) = fvExp e `Set.union` fvType ty
fvExp (LetP pat e prop) = fvExp e `Set.union` (fvExp prop Set.\\ bsPat pat)
fvExp (QP _qt vars body) = fvBndrs vars `Set.union` (fvExp body Set.\\ Set.fromList vars)


fvPats :: [Pat] -> Set Var
fvPats = Set.unions . map fvPat

fvPat :: Pat -> Set Var
  -- I think it should be 'fvPolyType $ varType x' but that would require
  -- to fix the algorithm to work just with 'Var p'
  -- other way would be to use type-classes... but it may have problems
fvPat (VarPat _) = Set.empty
fvPat (LitPat _) = Set.empty
fvPat (ConPat _con _ ps) = fvPats ps
fvPat (TuplePat _ ps) = fvPats ps
fvPat (ParenPat p) = fvPat p


bsPats :: [Pat] -> Set Var
bsPats = Set.unions . map bsPat

bsPat :: Pat -> Set Var
bsPat (VarPat x) = Set.singleton x
bsPat (LitPat _) = Set.empty
bsPat (ConPat _con _ ps) = bsPats ps
bsPat (TuplePat _ ps) = bsPats ps
bsPat (ParenPat p) = bsPat p

fvAlts :: [Alt] -> Set Var
fvAlts = Set.unions . map fvAlt

fvAlt :: Alt -> Set Var
fvAlt (Alt pat rhs) = fvPat pat `Set.union` (fvRhs rhs Set.\\ bsPat pat)

fvRhs :: Rhs -> Set Var
fvRhs (Rhs _ expr) = fvExp expr

fvGuardedRhss :: GuardedRhss -> Set Var
fvGuardedRhss (GuardedRhss grhss elserhs)
  = Set.unions $ fvElse elserhs : map fvGuardedRhs grhss 

fvGuardedRhs :: GuardedRhs -> Set Var
fvGuardedRhs (GuardedRhs g e) = fvExps [g,e]

fvElse :: Maybe Exp -> Set Var
fvElse = fvMaybeExp

fvTypes :: [Type c] -> Set Var
fvTypes = Set.unions . map fvType

fvType :: Type c -> Set Var
fvType (VarTy _) = Set.empty
fvType (ConTy _ args) = fvTypes args
fvType (PredTy pat ty mbprop)
  = fvType ty `Set.union` (fvMaybeExp mbprop Set.\\ bsPat pat)
fvType (FunTy dom range)
  = fvDom dom `Set.union` (fvType range Set.\\ bsDom dom)
fvType (ListTy ty) = fvType ty
fvType (TupleTy ds) = fvDoms ds
  -- this case may be tricky ...
fvType (ForallTy _tvs ty) = fvType ty

fvDoms :: [Dom] -> Set Var
fvDoms []     = Set.empty
fvDoms (d:ds) = fvDom d `Set.union` (fvDoms ds Set.\\ bsDom d)

fvDom :: Dom -> Set Var
fvDom (Dom Nothing ty Nothing) = fvType ty
fvDom (Dom (Just pat) ty mbprop)
  = fvType ty `Set.union` (fvMaybeExp mbprop Set.\\ bsPat pat)
fvDom _other = undefined -- impossible

bsDom :: Dom -> Set Var
bsDom (Dom mbpat _ty _mbprop) = maybe Set.empty bsPat mbpat
