
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :  H.Syntax.Pretty
-- Copyright   :  (c) Iago Abal 2011-2012
-- License     :  BSD3
--
-- Maintainer  :  Iago Abal, iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- H! pretty printing.

module H.Syntax.Pretty
  where

import H.Syntax.AST
import H.Syntax.Phase

import Pretty



-- * Pretty-names class

class (Pretty (VAR p), PrettyBndr (VAR p), Pretty (CON p),
      Pretty (TyVAR p), PrettyBndr (TyVAR p), Pretty (TyCON p),
      Pretty(GoalNAME p)) => PrettyNames p where

instance PrettyNames Pr where
instance PrettyNames Rn where
instance PrettyNames Tc where
instance PrettyNames Ti where


-- * Variables

instance Pretty (Var p) where
  pretty v@(V _ _ False) = pretty $ varName v
  pretty v@(V _ _ True) = char '!' <> pretty (varName v)

instance PrettyNames p => PrettyBndr (Var p) where
  prettyBndr x = parens $ pretty x <> colon <> pretty (varType x)

instance Pretty TyVar where
  pretty tv@(TyV _ _ False) = pretty $ tyVarName tv
  pretty tv@(TyV _ _ True) = char '\'' <> pretty (tyVarName tv)

instance PrettyBndr TyVar where
  prettyBndr tv = parens $ pretty tv <> colon <> pretty (tyVarKind tv)


-- * Modules

instance PrettyNames p => Pretty (Module p) where
  pretty (Module _pos modName decls) =
    topLevel (ppModuleHeader modName)
       (map pretty decls)

ppModuleHeader :: ModuleName ->  Doc
ppModuleHeader modName = mySep [
  text "module",
  pretty modName,
  text "where"]

instance Pretty ModuleName where
  pretty (ModName modName) = text modName


-- * Declarations

instance PrettyNames p => Pretty (Decl p) where
  pretty (TypeDecl _loc name nameList htype) =
    blankline $
    mySep ( [text "type", pretty name]
      ++ map prettyBndr nameList
      ++ [equals, pretty htype])
  pretty (DataDecl _loc name nameList constrList) =
    blankline $
    mySep ( [text "data", pretty name]
      ++ map prettyBndr nameList)
      <+> myVcat (zipWith (<+>) (equals : repeat (char '|'))
               (map pretty constrList))
--   pretty (TypeSig pos name polyType)
--     = blankline $
--       mySep [pretty name, text ":", pretty polyType]
  pretty (ValDecl bind) = blankline $ pretty bind
  pretty (GoalDecl _pos goaltype gname ptctyps prop)
    = blankline $
        myFsep $ [pretty goaltype, pretty gname] ++ pp_typs ++ [equals, pretty prop]
    where pp_typs = case ptctyps of
                        NoPostTc    -> []
                        PostTc typs -> map (\tv -> char '@' <> pretty tv) typs

instance PrettyNames p => Pretty (ConDecl p) where
  pretty (ConDeclIn _pos name typeList) =
    mySep $ pretty name : map (prettyPrec prec_atype) typeList
  pretty (ConDecl _pos name typeList) =
    mySep $ pretty name : map (prettyPrec prec_atype) typeList

instance Pretty GoalType where
  pretty TheoremGoal = text "theorem"
  pretty LemmaGoal   = text "lemma"


-- * Binds

instance PrettyNames p => Pretty (Bind p) where
  pretty (FunBind _rec fun sig _ matches) =
         ppTypeSig fun sig
      $$ ppBindings (map (ppMatch fun) matches)
  pretty (PatBind _pos pat (Rhs _ grhs whereDecls)) =
    myFsep [pretty pat, ppGRhs ValDef grhs]
        $$$ ppWhere whereDecls

ppTypeSig :: PrettyNames p => NAME p -> TypeSig p -> Doc
ppTypeSig _fun NoTypeSig = empty
ppTypeSig  fun (TypeSig _loc polyty) = mySep [pretty fun, text ":", pretty polyty]

ppMatch :: PrettyNames p => NAME p -> Match p -> Doc
ppMatch fun (Match _pos ps (Rhs _ grhs whereDecls)) =
    myFsep (lhs ++ [ppGRhs ValDef grhs])
    $$$ ppWhere whereDecls
      where
    lhs = pretty fun : map (prettyPrec 2) ps

ppWhere :: PrettyNames p => WhereBinds p -> Doc
ppWhere [] = empty
ppWhere l  = nest 2 (text "where" $$$ ppBody whereIndent (map pretty l))


-- * Expressions

instance PrettyNames p => Pretty (QVar p) where
  pretty (QVar v Nothing)   = prettyBndr v
  pretty (QVar v (Just ty)) = parens $ pretty v <> char ':' <> pretty ty

isAtomicExp :: Exp p -> Bool
isAtomicExp (Var _)   = True
isAtomicExp (Con _)   = True
isAtomicExp (Op _)    = True
isAtomicExp (Lit _)   = True
isAtomicExp ElseGuard = True
isAtomicExp (Tuple _ _) = True
isAtomicExp (List _ _) = True
isAtomicExp (Paren _) = True
isAtomicExp (LeftSection _ _) = True
isAtomicExp (RightSection _ _) = True
isAtomicExp (EnumFromTo _ _) = True
isAtomicExp (EnumFromThenTo _ _ _) = True
isAtomicExp _other    = False

ppParenExp :: PrettyNames p => Exp p -> Doc
ppParenExp e | isAtomicExp e = pretty e
             | otherwise     = parens $ pretty e

instance PrettyNames p => Pretty (Exp p) where
  pretty (Lit lit) = pretty lit
  pretty ElseGuard = text "else"
    -- no other possibility for prefix ops
  pretty (PrefixApp (Op op) a) = myFsep [pretty op, pretty a]
  pretty (PrefixApp _other  _) = undefined -- impossible
  pretty (InfixApp a opE b)
    = case opE of
          Op op  -> myFsep [pretty a, pretty op, pretty b]
          _other -> myFsep [pretty opE, ppParenExp a, ppParenExp b]
  pretty (App a b) = myFsep [pretty a, ppParenExp b]
  pretty (Lam _loc patList rhs) = myFsep $
    char '\\' : map pretty patList ++ [text "->", ppRhs LamAbs rhs]
  pretty (TyApp e tys) = myFsep $ pretty e : map (\ty -> char '@' <> ppAType ty) tys
  pretty (TyLam tvs body) = myFsep $ char '\\' : map prettyBndr tvs ++ [text "->", pretty body]
  pretty (Let expList letBody) =
    myFsep [text "let" <+> ppBody letIndent (map pretty expList),
      text "in", pretty letBody]
  pretty (Ite _ cond thenexp elsexp) =
    myFsep [text "if", pretty cond,
      text "then", pretty thenexp,
      text "else", pretty elsexp]
  pretty (If _ grhss) = myFsep [text "if", ppGuardedRhss IfExp grhss]
  pretty (Case cond _ptcty altList) =
    myFsep [text "case", pretty cond, text "of"]
    $$$ ppBody caseIndent (map pretty altList)
  -- Constructors & Vars
  pretty (Var var) = pretty var
  pretty (Con con) = pretty con
  pretty (Op op)   = ppPrefixOp op
  pretty (Tuple _ expList) = parenList . map pretty $ expList
  pretty (Paren e) = parens . pretty $ e
  pretty (LeftSection e opE) -- = parens (pretty e <+> pretty op)
      = case opE of
          Op op  -> parens (pretty e <+> pretty op)
          _other -> myFsep [pretty opE, pretty e]
  pretty (RightSection opE e) -- = parens (pretty op <+> pretty e)
      = case opE of
          Op op  -> parens (pretty op <+> pretty e)
          _other -> hang (hsep [text "( \\ x_ ->", pretty opE, text "x_"])
                         4 (pretty e <> rparen)
  -- Lists
  pretty (List _ list) =
    bracketList . punctuate comma . map pretty $ list
  pretty (EnumFromTo from to) =
    bracketList [pretty from, text "..", pretty to]
  pretty (EnumFromThenTo from thenE to) =
    bracketList [pretty from <> comma, pretty thenE,
           text "..", pretty to]
  pretty (Coerc _pos e ty) =
    myFsep [pretty e, text ":", pretty ty]
  pretty (QP quant patList body)
    = myFsep $ pretty quant : map pretty patList ++ [text ",", pretty body]

-- ** Literals

instance Pretty Lit where
  pretty (IntLit i) = integer i

-- ** Right hand side

data RhsContext = ValDef
                | LamAbs
                | CaseAlt
                | IfExp

rhsSepSym :: RhsContext -> Doc
rhsSepSym ValDef  = equals
rhsSepSym LamAbs  = text "->"
rhsSepSym CaseAlt = text "->"
rhsSepSym IfExp   = text "->"

ppRhs :: PrettyNames p => RhsContext -> Rhs p -> Doc
ppRhs ctx (Rhs _ grhs whereDecls) = ppGRhs ctx grhs $$$ ppWhere whereDecls

ppGRhs :: PrettyNames p => RhsContext -> GRhs p -> Doc
ppGRhs ctx (UnGuarded e)   = rhsSepSym ctx <+> pretty e
ppGRhs ctx (Guarded grhss) = ppGuardedRhss ctx grhss

ppGuardedRhss :: PrettyNames p => RhsContext -> GuardedRhss p -> Doc
ppGuardedRhss ctx (GuardedRhssIn guardList)
  = myVcat $ map (ppGuardedRhs ctx) guardList
ppGuardedRhss ctx (GuardedRhss guardList elserhs)
  = myVcat $ map (ppGuardedRhs ctx) guardList ++ [ppElse ctx elserhs]

ppGuardedRhs :: PrettyNames p => RhsContext -> GuardedRhs p -> Doc
ppGuardedRhs ctx (GuardedRhs _pos guard body) =
    myFsep [char '|', pretty guard, rhsSepSym ctx, pretty body]

ppElse :: PrettyNames p => RhsContext -> Else p -> Doc
ppElse  ctx (Else _pos body)
  = myFsep [char '|', text "else", rhsSepSym ctx, pretty body]
ppElse _ctx  NoElse   = empty

-- ** Logical quantifiers

instance Pretty Quantifier where
  pretty ForallQ = text "forall"
  pretty ExistsQ = text "exists"


-- * Patterns

instance PrettyNames p => Pretty (Pat p) where
    -- special case
--   prettyPrec _ (SigPat (VarPat var) ty) =
--     parens $ myFsep [pretty var, text ":", pretty ty]
    -- special case
--   prettyPrec _ (SigPat (AsPat var pat) ty) =
--     parens $ myFsep [hcat [pretty var, char '@', pretty pat], text ":", pretty ty]
  prettyPrec _ (VarPat var) = prettyBndr var
  prettyPrec _ (LitPat lit) = pretty lit
  prettyPrec p (InfixCONSPat _ a b) = parensIf (p > 0) $
    myFsep [pretty a, text "::", pretty b]
  prettyPrec _ (ConPat con _ []) = pretty con
  prettyPrec p (ConPat con _ ps) = parensIf (p > 1) $
    myFsep (pretty con : map pretty ps)
  prettyPrec _ (TuplePat ps _) = parenList . map pretty $ ps
  prettyPrec _ (ListPat ps _) =
    bracketList . punctuate comma . map pretty $ ps
  prettyPrec _ (ParenPat p) = parens . pretty $ p
  -- special case that would otherwise be buggy
  prettyPrec _ (AsPat var pat) =
    hcat [prettyBndr var, char '@', pretty pat]
  prettyPrec _ WildPatIn     = char '_'
  prettyPrec _ (WildPat var) = pretty var
--   prettyPrec _ (SigPat pat ty) =
--     parens $ myFsep [pretty pat, text ":", pretty ty]


-- * Alternatives

instance PrettyNames p => Pretty (Alt p) where
  pretty (Alt _pos pat rhs) =
    myFsep [pretty pat, ppRhs CaseAlt rhs]    -- is this pretty printed correctly ?


-- * Data constructors

instance Pretty BuiltinCon where
  pretty UnitCon  = text "()"
  pretty FalseCon = text "False"
  pretty TrueCon  = text "True"
  pretty NilCon   = text "[]"
  pretty ConsCon  = text "(::)"

instance Pretty (NAME p) => Pretty (Con p) where
  pretty (UserCon name)    = pretty name
  pretty (BuiltinCon bcon) = pretty bcon

instance Pretty (NAME p) => Pretty (TcCon p) where
  pretty = pretty . tcConCon


-- * Operators

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


-- * Tyoes

ppDomType :: PrettyNames p => Dom p -> Doc
ppDomType = prettyPrec prec_btype

ppAType :: PrettyNames p => Type c p -> Doc
ppAType = prettyPrec prec_atype

-- precedences for types
prec_btype, prec_atype :: Int
prec_btype = 1  -- left argument of ->,
    -- or either argument of an infix data constructor
prec_atype = 2  -- argument of type or data constructor, or of a class

-- instance PrettyNames p => Pretty (Sigma p) where
--   pretty (ForallTy [] ty)
--     = pretty ty
--   pretty (ForallTy typarams ty)
--     = myFsep [text "forall", mySep $ map pretty typarams, char '.', pretty ty]

instance PrettyNames p => Pretty (Type c p) where
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
  prettyPrec p (AppTyIn a b) = parensIf (p > prec_btype) $
      myFsep [pretty a, ppAType b]
  prettyPrec _ (ConTy tc []) = pretty tc
  prettyPrec p (ConTy tc args) = parensIf (p > prec_btype) $
      myFsep $ pretty tc : map ppAType args
  prettyPrec _ (VarTy name) = pretty name
  prettyPrec _ (ConTyIn tycon) = pretty tycon
  prettyPrec _ (ParenTy ty) = pretty ty
  prettyPrec _ (MetaTy mtv) = pretty mtv
  prettyPrec _ (ForallTy typarams ty)
    = myFsep [text "forall", mySep $ map pretty typarams, char '.', pretty ty]

instance PrettyNames p => Pretty (Dom p) where
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

ppTupleDom :: PrettyNames p => Dom p -> Doc
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

-- ** Meta type variables

instance Pretty MetaTyVar where
  pretty (MetaTyV name _ _) = char '?' <> pretty name


-- * Type constructors

instance Pretty BuiltinTyCon where
  pretty UnitTyCon = text "()"
  pretty BoolTyCon = text "Bool"
  pretty IntTyCon  = text "Int"
  pretty NatTyCon  = text "Nat"
  pretty ListTyCon = text "[]"    -- should not happen...

instance Pretty (TyVAR p) => Pretty (TyName p) where
  pretty (UserTyCon name) = pretty name
  pretty (BuiltinTyCon tycon) = pretty tycon

instance Pretty (TyName p) => Pretty (TyCon p) where
  pretty = pretty . tyConName


-- * Kinds

instance Pretty Kind where
  prettyPrec _ TypeKi = char '*'
  prettyPrec p (FunKi k1 k2)
    = parensIf (p > 0) $
        myFsep [prettyPrec 1 k1, text "->", pretty k2]
