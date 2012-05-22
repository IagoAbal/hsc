{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}

-- | Pretty-printing for Core syntax
module Core.Syntax.Pretty where


import Core.Syntax.AST
  -- TODO: Remove this dependency
import {-# SOURCE #-} Core.Syntax.Built

import Pretty

import Data.Foldable ( toList )
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IMap



-- * Variables

instance Pretty Var where
  pretty v@(V _ _ False) = pretty $ varName v
  pretty v@(V _ _ True)  = char '!' <> pretty (varName v)

instance PrettyBndr Var where
  prettyBndr x = pretty x <> colon <> pretty (varType x)

instance Show Var where
  show = render . pretty

instance Pretty TyVar where
  pretty tv@(TyV _ _ False) = pretty $ tyVarName tv
  pretty tv@(TyV _ _ True) = char '\'' <> pretty (tyVarName tv)

instance PrettyBndr TyVar where
  prettyBndr tv = parens $ pretty tv <> colon <> pretty (tyVarKind tv)

-- ** Params

ppTyParams :: TyParams -> [Doc]
ppTyParams = map (\tv -> char '@' <> pretty tv)

-- * Modules

instance Pretty Module where
  pretty (Module{modName,modDecls}) =
    topLevel (ppModuleHeader modName)
       (map pretty modDecls)

ppModuleHeader :: ModuleName ->  Doc
ppModuleHeader name = mySep [
  text "module",
  pretty name,
  text "where"]

instance Pretty ModuleName where
  pretty (ModName name) = text name


-- * Declarations

instance Pretty Decl where
  pretty (TypeDecl name nameList htype) =
    blankline $
    mySep ( [text "type", pretty name]
      ++ map prettyBndr nameList
      ++ [equals, pretty htype])
  pretty (DataDecl name nameList constrList) =
    blankline $
    mySep ( [text "data", pretty name]
      ++ map prettyBndr nameList)
      <+> myVcat (zipWith (<+>) (equals : repeat (char '|'))
               (map pretty constrList))
  pretty (ValDecl bind) = blankline $ pretty bind
  pretty (GoalDecl goaltype gname typs prop)
    = blankline $ myFsep $ [pretty goaltype, pretty gname]
                            ++ ppTyParams typs
                            ++ [equals, pretty prop]

instance Pretty GoalType where
  pretty TheoremGoal = text "theorem"
  pretty LemmaGoal   = text "lemma"

instance Pretty Bind where
  pretty (FunBind _rec fun typs args (Rhs _tau expr))
    =  pretty fun <> colon <> pretty (varType fun)
    $$ myFsep ([pretty fun] ++ ppTyParams typs ++ pp_args
                ++ [ppRhsExp ValDef expr])
--     $$$ ppWhere whereDecls
    where pp_args = map pretty args
--   pretty (PatBind pat (Rhs _tau expr whereDecls)) =
--     myFsep [pretty pat, ppRhsExp ValDef expr]
--         $$$ ppWhere whereDecls

--ppMatch :: Var -> Match -> Doc
--ppMatch fun (Match  ps (Rhs _tau expr whereDecls)) =
--    myFsep (lhs ++ [ppGRhs ValDef grhs])
--    $$$ ppWhere whereDecls
--      where
--    lhs = prettyBndr fun : map (prettyPrec 2) ps

-- ppWhere :: WhereBinds -> Doc
-- ppWhere [] = empty
-- ppWhere l  = nest 2 (text "where" $$$ ppBody whereIndent (map pretty l))

instance Pretty ConDecl where
  pretty (ConDecl name typeList) =
    mySep $ pretty name : map (prettyPrec prec_atype) typeList


-- * Expressions

isAtomicExp :: Exp -> Bool
isAtomicExp (Var _)   = True
isAtomicExp (Con _)   = True
isAtomicExp (Lit _)   = True
isAtomicExp (Tuple _ _) = True
isAtomicExp (List _ _) = True
isAtomicExp (Paren _) = True
isAtomicExp (EnumFromTo _ _) = True
isAtomicExp (EnumFromThenTo _ _ _) = True
isAtomicExp _other    = False

ppParenExp :: Exp -> Doc
ppParenExp e | isAtomicExp e = pretty e
             | otherwise     = parens $ pretty e

ppOpExp :: OpExp -> Doc
ppOpExp (OpExp tys op) = myFsep $ pretty op : map (\ty -> char '@' <> ppAType ty) tys

ppInfixApp :: OpExp -> Exp -> Exp -> Doc
ppInfixApp (OpExp [] op) a b = myFsep [pretty a, pretty op, pretty b]
ppInfixApp op a b
  = myFsep [ppParenExp a, ppOpExp op, ppParenExp b]

instance Pretty Exp where
  pretty (Lit lit) = pretty lit
    -- no other possibility for prefix ops
  pretty (PrefixApp op a) = myFsep [ppOpExp op, pretty a]
  pretty (InfixApp a op b) = ppInfixApp op a b
  pretty (App a b) = myFsep [pretty a, ppParenExp b]
  pretty (Lam patList rhs) = myFsep $
    char '\\' : map pretty patList ++ [ppRhs LamAbs rhs]
  pretty (TyApp e tys) = myFsep $ pretty e : map (\ty -> char '@' <> ppAType ty) tys
  pretty (TyLam tvs body) = myFsep $ char '\\' : map (parens . prettyBndr) tvs ++ [text "->", pretty body]
  pretty (Let expList letBody) =
    myFsep [text "let" <+> ppBody letIndent (map pretty expList),
      text "in", pretty letBody]
  pretty (Ite _ cond thenexp elsexp) =
    myFsep [text "if", pretty cond,
      text "then", pretty thenexp,
      text "else", pretty elsexp]
  pretty (If _ grhss) = myFsep [text "if", ppGuardedRhss grhss]
  pretty (Case _ cond altList) =
    myFsep [text "case", pretty cond, text "of"]
    $$$ ppBody caseIndent (map pretty altList)
  -- Constructors & Vars
  pretty (Var var) = pretty var
  pretty (Con con) = pretty con
  pretty (Tuple _ expList) = parenList . map pretty $ expList
  pretty (Paren e) = parens . pretty $ e
  -- Lists
  pretty (List _ list) =
    bracketList . punctuate comma . map pretty $ list
  pretty (EnumFromTo from to) =
    bracketList [pretty from, text "..", pretty to]
  pretty (EnumFromThenTo from thenE to) =
    bracketList [pretty from <> comma, pretty thenE,
           text "..", pretty to]
  pretty (Coerc e ty) =
    myFsep [pretty e, text ":", pretty ty]
  pretty (LetP pat e prop)
    = myFsep [text "letP", pretty pat, char '=', pretty e, text "in", pretty prop]
  pretty (QP quant xs body)
    = myFsep $ pretty quant : map ppr_qvar xs ++ [text ",", pretty body]
    where ppr_qvar x = parens $ prettyBndr x

instance Show Exp where
  show = render . pretty

-- ** RHS

data RhsContext = ValDef
                | LamAbs
                | CaseAlt
                | IfExp

rhsSepSym :: RhsContext -> Doc
rhsSepSym ValDef  = equals
rhsSepSym LamAbs  = text "->"
rhsSepSym CaseAlt = text "->"
rhsSepSym IfExp   = text "->"

ppRhs :: RhsContext -> Rhs -> Doc
ppRhs ctx (Rhs _tau expr)
  = ppRhsExp ctx expr
--   $$$ ppWhere whereDecls

ppRhsExp :: RhsContext -> Exp -> Doc
ppRhsExp ctx e = rhsSepSym ctx <+> pretty e

--ppGRhs :: RhsContext -> GRhs -> Doc
--ppGRhs ctx (UnGuarded e)   = rhsSepSym ctx <+> pretty e
--ppGRhs ctx (Guarded grhss) = ppGuardedRhss ctx grhss

ppGuardedRhss :: GuardedRhss -> Doc
ppGuardedRhss (GuardedRhss guardList elserhs)
 = myVcat $ map ppGuardedRhs guardList ++ [ppElse elserhs]

ppGuardedRhs :: GuardedRhs -> Doc
ppGuardedRhs (GuardedRhs guard body)
  = myFsep [char '|', pretty guard, text "->", pretty body]

ppElse :: Maybe Exp -> Doc
ppElse (Just body)
  = myFsep [char '|', text "else", text "->", pretty body]
ppElse Nothing = empty

-- ** Patterns

instance Pretty Pat where
  prettyPrec _ (VarPat var) = pretty var -- parens $ prettyBndr var
  prettyPrec _ (LitPat lit) = pretty lit
--   prettyPrec p (InfixCONSPat _ a b) = parensIf (p > 0) $
--     myFsep [pretty a, text "::", pretty b]
  prettyPrec _ (ConPat _taus con []) = pretty con
  prettyPrec p (ConPat _taus con ps) = parensIf (p > 1) $
    myFsep (pretty con : map pretty ps)
  prettyPrec _ (TuplePat _tau ps) = parenList . map pretty $ ps
--   prettyPrec _ (ListPat _tau ps) =
--     bracketList . punctuate comma . map pretty $ ps
  prettyPrec _ (ParenPat p) = parens . pretty $ p

instance Pretty Alt where
  pretty (Alt pat rhs) =
    myFsep [pretty pat, ppRhs CaseAlt rhs]    -- is this pretty printed correctly ?

-- ** Literals

instance Pretty Lit where
  pretty (IntLit i) = integer i

-- ** Data constructors

instance Pretty BuiltinCon where
  pretty UnitCon  = text "()"
  pretty FalseCon = text "False"
  pretty TrueCon  = text "True"
  pretty NilCon   = text "[]"
  pretty ConsCon  = text "(::)"

instance Pretty Con where
  pretty (UserCon name)    = pretty name
  pretty (BuiltinCon bcon) = pretty bcon

-- ** Built-in operators

instance Pretty Op where
  pretty (BoolOp bop) = pretty bop
  pretty (IntOp iop)  = pretty iop
  pretty CONSOp       = text "::"

ppPrefixOp :: Op -> Doc
ppPrefixOp = parens . pretty

instance Pretty BoolOp where
  pretty NotB = char '~'
  pretty OrB  = text "||"
  pretty AndB = text "&&"
  pretty ImpB = text "==>"
  pretty IffB = text "<=>"
  pretty EqB  = text "=="
  pretty NeqB = text "/="
  pretty LtB  = char '<'
  pretty LeB  = text "<="
  pretty GtB  = char '>'
  pretty GeB  = text ">="

instance Pretty IntOp where
  pretty NegI = char '-'
  pretty AddI = char '+'
  pretty SubI = char '-'
  pretty MulI = char '*'
  pretty DivI = char '/'
  pretty ModI = char '%'
  pretty ExpI = char '^'

-- ** Logical quantifiers

instance Pretty Quantifier where
  pretty ForallQ = text "forall"
  pretty ExistsQ = text "exists"


-- * Types

ppDomType :: Dom -> Doc
ppDomType = prettyPrec prec_btype

ppAType :: Type c -> Doc
ppAType = prettyPrec prec_atype

-- precedences for types
prec_btype, prec_atype :: Int
prec_btype = 1  -- left argument of ->,
    -- or either argument of an infix data constructor
prec_atype = 2  -- argument of type or data constructor, or of a class

instance Pretty (Type c) where
  prettyPrec _ (PredTy (VarPat var) ty mb_prop)
    = braces $ mySep ([pretty var, char ':', pretty ty] ++ pp_prop)
    where pp_prop = case mb_prop of
                        Nothing -> [empty]
                        Just prop -> [char '|', pretty prop]
  prettyPrec _ (PredTy pat ty mb_prop)
    = braces $ mySep ([pretty pat, char ':', pretty ty] ++ pp_prop)
    where pp_prop = case mb_prop of
                        Nothing -> [empty]
                        Just prop -> [char '|', pretty prop]
  prettyPrec p (FunTy a b) = parensIf (p > 0) $
    myFsep [ppDomType a, text "->", pretty b]
  prettyPrec _ (ListTy a)  = brackets $ pretty a
  prettyPrec _ (TupleTy l) = parenList . map ppTupleDom $ l
  prettyPrec _ (ConTy tc []) = pretty tc
  prettyPrec p (ConTy tc args) = parensIf (p > prec_btype) $
      myFsep $ pretty tc : map ppAType args
  prettyPrec _ (VarTy name) = pretty name
  prettyPrec _ (ForallTy typarams ty)
    = myFsep [text "forall", mySep $ map pretty typarams, char '.', pretty ty]

instance Pretty Dom where
  prettyPrec p (Dom Nothing ty Nothing) = prettyPrec p ty
  -- dependent arrow
  prettyPrec _p (Dom (Just (VarPat var)) ty mb_prop)
    = braces $ mySep ([pretty var, char ':', pretty ty] ++ pp_prop)
    where pp_prop = case mb_prop of
                        Nothing -> [empty]
                        Just prop -> [char '|', pretty prop]
  prettyPrec _p (Dom (Just pat) ty mb_prop)
    = braces $ mySep ([pretty pat, char ':', pretty ty] ++ pp_prop)
    where pp_prop = case mb_prop of
                        Nothing -> [empty]
                        Just prop -> [char '|', pretty prop]
  prettyPrec _p _other = undefined

ppTupleDom :: Dom -> Doc
ppTupleDom (Dom Nothing ty Nothing) = pretty ty
  -- special case
ppTupleDom (Dom (Just (VarPat var)) ty mb_prop)
  = mySep ([pretty var, char ':', pretty ty] ++ pp_prop)
  where pp_prop = case mb_prop of
                      Nothing -> [empty]
                      Just prop -> [char '|', pretty prop]
ppTupleDom (Dom (Just pat) ty mb_prop)
  = mySep ([pretty pat, char ':', pretty ty] ++ pp_prop)
  where pp_prop = case mb_prop of
                      Nothing -> [empty]
                      Just prop -> [char '|', pretty prop]
ppTupleDom _other = undefined -- impossible

-- ** Type constructors

instance Pretty TyName where
  pretty (UserTyCon name) = pretty name
  pretty (BuiltinTyCon tycon) = pretty tycon

instance Pretty BuiltinTyCon where
  pretty UnitTyCon = text "()"
  pretty BoolTyCon = text "Bool"
  pretty IntTyCon  = text "Int"
  pretty NatTyCon  = text "Nat"
  pretty ListTyCon = text "[]"    -- should not happen...

instance Pretty TyCon where
  pretty = pretty . tyConName


-- * Kinds

instance Pretty Kind where
  prettyPrec _ TypeKi = char '*'
  prettyPrec p (FunKi k1 k2)
    = parensIf (p > 0) $
        myFsep [prettyPrec 1 k1, text "->", pretty k2]

-- * TCCs

instance Pretty TccHypoThing where
  pretty (ForAll xs)
    = myFsep $ punctuate comma $ map prettyBndr xs
  pretty (LetIn binds)
    = text "let" <+> ppBody letIndent (map pretty binds)
  pretty (Facts props)
    = vcat $ map pretty props

instance Pretty TCC where
  pretty tcc@(CoercionTCC srcCtxt propCtxt expr act_ty exp_ty prop)
    = text "COERCION TCC"
    $$ brackets (text srcCtxt)
    $$ char '>' <+> text "expression:" <+> pretty expr
    $$ char '>' <+> text "inferred type:" <+> pretty act_ty
    $$ char '>' <+> text "required type:" <+> pretty exp_ty
    $$ text "|------------------------------------------------------"
    $$ pretty (tcc2prop tcc)
  pretty tcc@(CompletenessTCC srcCtxt propCtxt prop)
    = text "COMPLETENESS TCC"
    $$ brackets (text srcCtxt)
--     $$ (vcat $ map pretty $ toList propCtxt)
    $$ text "|------------------------------------------------------"
    $$ pretty (tcc2prop tcc)

instance Pretty (IntMap TCC) where
  pretty tccMap = vcat $ map (blankline . pp_tcc) $ IMap.toList tccMap
    where pp_tcc (i,tcc) = int i <> char '#' $$ pretty tcc
