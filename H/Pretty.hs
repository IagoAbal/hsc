{-# OPTIONS_GHC -w #-}
{-# LANGUAGE GADTs,
						 TypeOperators,
						 FlexibleContexts,
						 FlexibleInstances,
						 TypeFamilies,
						 UndecidableInstances
						 #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Pretty
-- Copyright   :  (c) The GHC Team, Noel Winstanley 1997-2000
--                (c) Iago Abal, 2011
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Pretty printer for H!.
--
-----------------------------------------------------------------------------

module H.Pretty
	( -- * Pretty printing
		Pretty,
		prettyPrintStyleMode, prettyPrintWithMode, prettyPrint,
		-- * Pretty-printing styles (from "Text.PrettyPrint.HughesPJ")
		P.Style(..), P.style, P.Mode(..),
		-- * Haskell formatting modes
		PPHsMode(..), Indent, PPLayout(..), defaultMode
	) where

import H.Syntax
import H.Parser.ParseMonad( ParseResult(..) )
import Name
import Sorted

import qualified Text.PrettyPrint as P

infixl 5 $$$

-----------------------------------------------------------------------------

-- | Varieties of layout we can use.
data PPLayout = PPOffsideRule	-- ^ classical layout
	      | PPSemiColon	-- ^ classical layout made explicit
	      | PPInLine	-- ^ inline decls, with newlines between them
	      | PPNoLayout	-- ^ everything on a single line
	      deriving Eq

type Indent = Int

-- | Pretty-printing parameters.
--
-- /Note:/ the 'onsideIndent' must be positive and less than all other indents.
data PPHsMode = PPHsMode {
				-- | indentation of the body of a
				-- @case@ expression
		caseIndent :: Indent,
				-- | indentation of the declarations in a
				-- @let@ expression
		letIndent :: Indent,
				-- | indentation of the declarations in a
				-- @where@ clause
		whereIndent :: Indent,
				-- | indentation added for continuation
				-- lines that would otherwise be offside
		onsideIndent :: Indent,
				-- | blank lines between statements?
		spacing :: Bool,
				-- | Pretty-printing style to use
		layout :: PPLayout,
				-- | add GHC-style @LINE@ pragmas to output?
		linePragmas :: Bool,
				-- | not implemented yet
		comments :: Bool
		}

-- | The default mode: pretty-print using the offside rule and sensible
-- defaults.
defaultMode :: PPHsMode
defaultMode = PPHsMode{
		      caseIndent = 4,
		      letIndent = 4,
		      whereIndent = 6,
		      onsideIndent = 2,
		      spacing = True,
		      layout = PPOffsideRule,
		      linePragmas = False,
		      comments = True
		      }

-- | Pretty printing monad
newtype DocM s a = DocM (s -> a)

instance Functor (DocM s) where
	 fmap f xs = do x <- xs; return (f x)

instance Monad (DocM s) where
	(>>=) = thenDocM
	(>>) = then_DocM
	return = retDocM

{-# INLINE thenDocM #-}
{-# INLINE then_DocM #-}
{-# INLINE retDocM #-}
{-# INLINE unDocM #-}
{-# INLINE getPPEnv #-}

thenDocM :: DocM s a -> (a -> DocM s b) -> DocM s b
thenDocM m k = DocM $ (\s -> case unDocM m $ s of a -> unDocM (k a) $ s)

then_DocM :: DocM s a -> DocM s b -> DocM s b
then_DocM m k = DocM $ (\s -> case unDocM m $ s of _ -> unDocM k $ s)

retDocM :: a -> DocM s a
retDocM a = DocM (\_s -> a)

unDocM :: DocM s a -> (s -> a)
unDocM (DocM f) = f

-- all this extra stuff, just for this one function.
getPPEnv :: DocM s s
getPPEnv = DocM id

-- So that pp code still looks the same
-- this means we lose some generality though

-- | The document type produced by these pretty printers uses a 'PPHsMode'
-- environment.
type Doc = DocM PPHsMode P.Doc

-- | Things that can be pretty-printed, including all the syntactic objects
-- in "Language.Haskell.Syntax".
class Pretty a where
	-- | Pretty-print something in isolation.
	pretty :: a -> Doc
	-- | Pretty-print something in a precedence context.
	prettyPrec :: Int -> a -> Doc
	pretty = prettyPrec 0
	prettyPrec _ = pretty

-- The pretty printing combinators

empty :: Doc
empty = return P.empty

nest :: Int -> Doc -> Doc
nest i m = m >>= return . P.nest i


-- Literals

text, ptext :: String -> Doc
text = return . P.text
ptext = return . P.text

char :: Char -> Doc
char = return . P.char

int :: Int -> Doc
int = return . P.int

integer :: Integer -> Doc
integer = return . P.integer

float :: Float -> Doc
float = return . P.float

double :: Double -> Doc
double = return . P.double

rational :: Rational -> Doc
rational = return . P.rational

-- Simple Combining Forms

parens, brackets, braces,quotes,doubleQuotes :: Doc -> Doc
parens d = d >>= return . P.parens
brackets d = d >>= return . P.brackets
braces d = d >>= return . P.braces
quotes d = d >>= return . P.quotes
doubleQuotes d = d >>= return . P.doubleQuotes

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

-- Constants

semi,comma,colon,space,equals :: Doc
semi = return P.semi
comma = return P.comma
colon = return P.colon
space = return P.space
equals = return P.equals

lparen,rparen,lbrack,rbrack,lbrace,rbrace :: Doc
lparen = return  P.lparen
rparen = return  P.rparen
lbrack = return  P.lbrack
rbrack = return  P.rbrack
lbrace = return  P.lbrace
rbrace = return  P.rbrace

-- Combinators

(<>),(<+>),($$),($+$) :: Doc -> Doc -> Doc
aM <> bM = do{a<-aM;b<-bM;return (a P.<> b)}
aM <+> bM = do{a<-aM;b<-bM;return (a P.<+> b)}
aM $$ bM = do{a<-aM;b<-bM;return (a P.$$ b)}
aM $+$ bM = do{a<-aM;b<-bM;return (a P.$+$ b)}

hcat,hsep,vcat,sep,cat,fsep,fcat :: [Doc] -> Doc
hcat dl = sequence dl >>= return . P.hcat
hsep dl = sequence dl >>= return . P.hsep
vcat dl = sequence dl >>= return . P.vcat
sep dl = sequence dl >>= return . P.sep
cat dl = sequence dl >>= return . P.cat
fsep dl = sequence dl >>= return . P.fsep
fcat dl = sequence dl >>= return . P.fcat

-- Some More

hang :: Doc -> Int -> Doc -> Doc
hang dM i rM = do{d<-dM;r<-rM;return $ P.hang d i r}

-- Yuk, had to cut-n-paste this one from Pretty.hs
punctuate :: Doc -> [Doc] -> [Doc]
punctuate _ []     = []
punctuate p (d1:ds) = go d1 ds
                   where
                     go d [] = [d]
                     go d (e:es) = (d <> p) : go e es

-- | render the document with a given style and mode.
renderStyleMode :: P.Style -> PPHsMode -> Doc -> String
renderStyleMode ppStyle ppMode d = P.renderStyle ppStyle . unDocM d $ ppMode

-- | render the document with a given mode.
renderWithMode :: PPHsMode -> Doc -> String
renderWithMode = renderStyleMode P.style

-- | render the document with 'defaultMode'.
render :: Doc -> String
render = renderWithMode defaultMode

-- | pretty-print with a given style and mode.
prettyPrintStyleMode :: Pretty a => P.Style -> PPHsMode -> a -> String
prettyPrintStyleMode ppStyle ppMode = renderStyleMode ppStyle ppMode . pretty

-- | pretty-print with the default style and a given mode.
prettyPrintWithMode :: Pretty a => PPHsMode -> a -> String
prettyPrintWithMode = prettyPrintStyleMode P.style

-- | pretty-print with the default style and 'defaultMode'.
prettyPrint :: Pretty a => a -> String
prettyPrint = prettyPrintWithMode defaultMode

fullRenderWithMode :: PPHsMode -> P.Mode -> Int -> Float ->
		      (P.TextDetails -> a -> a) -> a -> Doc -> a
fullRenderWithMode ppMode m i f fn e mD =
		   P.fullRender m i f fn e $ (unDocM mD) ppMode


fullRender :: P.Mode -> Int -> Float -> (P.TextDetails -> a -> a)
	      -> a -> Doc -> a
fullRender = fullRenderWithMode defaultMode

-- -------------------------  Pretty-Print a Module --------------------
instance (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => Pretty (Module p) where
	pretty (Module pos modName decls) =
		markLine pos $
		topLevel (ppModuleHeader modName)
			 (map pretty decls)


instance Pretty SrcLoc where
	pretty (SrcLoc file line column)
		= hcat [text file, char ':', int line, char ':', int column, char ':']

instance (Pretty a) => Pretty (ParseResult a) where
	pretty (ParseOk a) = pretty a
	pretty (ParseFailed loc errmsg) = mySep [pretty loc, text errmsg]

-- --------------------------  Module Header ------------------------------

ppModuleHeader :: ModuleName ->  Doc
ppModuleHeader modName = mySep [
	text "module",
	pretty modName,
	text "where"]

instance Pretty ModuleName where
	pretty (ModName modName) = text modName


-- -------------------------  Declarations ------------------------------

instance (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => Pretty (AnyDecl p) where
	pretty (AnyDecl decl) = pretty decl

instance (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => Pretty (Decl s p) where
	pretty (TypeDecl loc name nameList htype) =
		blankline $
		markLine loc $
		mySep ( [text "type", pretty name]
			++ map pretty nameList
			++ [equals, pretty htype])

	pretty (DataDecl loc name nameList constrList) =
		blankline $
		markLine loc $
		mySep ( [text "data", pretty name]
			++ map pretty nameList)
			<+> myVcat (zipWith (<+>) (equals : repeat (char '|'))
						   (map pretty constrList))

	pretty (TypeSig pos nameList polyType) =
		blankline $
		markLine pos $
		mySep ((punctuate comma . map pretty $ nameList)
		      ++ [text ":", pretty polyType])

	pretty (FunBind _rec fun matches) =
		ppBindings (map (ppMatch fun) matches)

	pretty (PatBind pos _rec pat (Rhs grhs whereDecls)) =
		markLine pos $
		myFsep [pretty pat, ppGRhs ValDef grhs]
				$$$ ppWhere whereDecls

-- GoalDecl :: SrcLoc -> NAME p -> GoalType -> PostTcTyParams p -> Prop p -> Decl Lg p
	pretty (GoalDecl pos goaltype gname _ptctys prop)
		= myFsep [ppGoalType goaltype, pretty gname, equals, pretty prop]
		where
				ppGoalType TheoremGoal = text "theorem"
				ppGoalType LemmaGoal   = text "lemma"


ppMatch :: (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => NAME p -> Match p -> Doc
ppMatch fun (Match pos ps (Rhs grhs whereDecls)) =
		markLine pos $
		myFsep (lhs ++ [ppGRhs ValDef grhs])
		$$$ ppWhere whereDecls
	    where
		lhs = pretty fun : map (prettyPrec 2) ps

ppWhere :: (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => [Decl s p] -> Doc
ppWhere [] = empty
ppWhere l  = nest 2 (text "where" $$$ ppBody whereIndent (map pretty l))

-- ------------------------- Data & Newtype Bodies -------------------------
instance (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => Pretty (ConDecl p) where
	pretty (ConDeclIn _pos name typeList) =
		mySep $ pretty name : map (prettyPrec prec_atype) typeList
	pretty (ConDecl _pos name typeList) =
		mySep $ pretty name : map (prettyPrec prec_atype) typeList

------------------------- Types -------------------------

ppDomType :: (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => Dom p -> Doc
ppDomType = prettyPrec prec_btype

ppAType :: (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => Type p -> Doc
ppAType = prettyPrec prec_atype

-- precedences for types
prec_btype, prec_atype :: Int
prec_btype = 1	-- left argument of ->,
		-- or either argument of an infix data constructor
prec_atype = 2	-- argument of type or data constructor, or of a class

instance (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => Pretty (PolyType p) where
	pretty (ForallTy [] ty)
		= pretty ty
	pretty (ForallTy typarams ty)
		= myFsep [text "forall", mySep $ map pretty typarams, char '.', pretty ty]

instance (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => Pretty (Type p) where
	prettyPrec _ (PredTy pat ty Nothing)
		= braces $ mySep [pretty pat, char ':', pretty ty]
	prettyPrec _ (PredTy pat ty (Just prop))
		= braces $ mySep [pretty pat, char ':', pretty ty, char '|', pretty prop]
	prettyPrec p (FunTyIn a b) = parensIf (p > 0) $
		myFsep [prettyPrec prec_btype a, text "->", pretty b]
	prettyPrec p (FunTy a b) = parensIf (p > 0) $
		myFsep [ppDomType a, text "->", pretty b]
	prettyPrec _ (ListTy a)  = brackets $ pretty a
	prettyPrec _ (TupleTy l) = parenList . map ppTupleDom $ l
	prettyPrec p (AppTy a b) = parensIf (p > prec_btype) $
			myFsep [pretty a, ppAType b]
	prettyPrec _ (VarTy name) = pretty name
	prettyPrec _ (ConTy tycon) = pretty tycon
	prettyPrec _ (ParenTy ty) = pretty ty
	-- MetaTy ?

	-- fun-dom
instance (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => Pretty (Dom p) where
	prettyPrec p (Dom Nothing ty Nothing) = prettyPrec p ty
	-- dependent arrow
	prettyPrec _p (Dom (Just pat) ty Nothing)
		= braces $ mySep [pretty pat, char ':', pretty ty]
	prettyPrec _p (Dom (Just pat) ty (Just prop))
		= braces $ mySep [pretty pat, char ':', pretty ty, char '|', pretty prop]
	prettyPrec _p _other = undefined

ppTupleDom :: (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => Dom p -> Doc
ppTupleDom (Dom Nothing ty Nothing) = pretty ty
ppTupleDom (Dom (Just pat) ty Nothing)
	= mySep [pretty pat, char ':', pretty ty]
ppTupleDom (Dom (Just pat) ty (Just prop))
	= mySep [pretty pat, char ':', pretty ty, char '|', pretty prop]

instance Pretty (TyVAR p) => Pretty (TyCon p) where
	pretty (UserTyCon name) = pretty name
	pretty (BuiltinTyCon tycon) = pretty tycon


instance Pretty BuiltinTyCon where
	pretty UnitTyCon = text "()"
	pretty BoolTyCon = text "Bool"
	pretty IntTyCon  = text "Int"
	pretty NatTyCon  = text "Nat"

-- ------------------------- Kinds -------------------------

instance Pretty Kind where
	prettyPrec _ TypeKi = char '*'
	prettyPrec p (FunKi k1 k2)
		= parensIf (p > 0) $
				myFsep [prettyPrec 1 k1, text "->", pretty k2]

-- ------------------------- Expressions -------------------------

data RhsContext = ValDef
                | CaseAlt
                | IfExp

rhsSepSym :: RhsContext -> Doc
rhsSepSym ValDef  = equals
rhsSepSym CaseAlt = text "->"
rhsSepSym IfExp   = text "->"

ppRhs :: (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => RhsContext -> Rhs p -> Doc
ppRhs ctx (Rhs grhs whereDecls) = ppGRhs ctx grhs $$$ ppWhere whereDecls

ppGRhs :: (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => RhsContext -> GRhs p -> Doc
ppGRhs ctx (UnGuarded e)   = rhsSepSym ctx <+> pretty e
ppGRhs ctx (Guarded grhss) = ppGuardedRhss ctx grhss

ppGuardedRhss :: (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => RhsContext -> GuardedRhss p -> Doc
ppGuardedRhss ctx (GuardedRhssIn guardList)
	= myVcat $ map (ppGuardedRhs ctx) guardList
ppGuardedRhss ctx (GuardedRhss guardList elserhs)
	= myVcat $ map (ppGuardedRhs ctx) guardList ++ [ppElse ctx elserhs]

ppGuardedRhs :: (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => RhsContext -> GuardedRhs p -> Doc
ppGuardedRhs ctx (GuardedRhs _pos guard body) =
		myFsep [char '|', pretty guard, rhsSepSym ctx, pretty body]

ppElse :: (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => RhsContext -> Else p -> Doc
ppElse ctx (Else _pos body)
	= myFsep [char '|', text "else", rhsSepSym ctx, pretty body]
ppElse ctx  NoElse   = empty



instance Pretty Lit where
	pretty (IntLit i) = integer i

instance (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => Pretty (Exp p) where
	pretty (Lit lit) = pretty lit
	pretty ElseGuard = text "else"
	-- lambda stuff
	pretty (PrefixApp op a) = myFsep [pretty op, pretty a]
	pretty (InfixApp a op b) = myFsep [pretty a, pretty op, pretty b]
	pretty (App a b) = myFsep [pretty a, pretty b]
	pretty (Lam _loc patList body) = myFsep $
		char '\\' : map pretty patList ++ [text "->", pretty body]
	-- keywords
	pretty (Let expList letBody) =
		myFsep [text "let" <+> ppBody letIndent (map pretty expList),
			text "in", pretty letBody]
	pretty (Ite cond thenexp elsexp) =
		myFsep [text "if", pretty cond,
			text "then", pretty thenexp,
			text "else", pretty elsexp]
	pretty (If grhss) = myFsep [text "if", ppGuardedRhss IfExp grhss]
	pretty (Case cond _ptcty altList) =
		myFsep [text "case", pretty cond, text "of"]
		$$$ ppBody caseIndent (map pretty altList)
	-- Constructors & Vars
	pretty (Var var) = pretty var
	pretty (Con con) = pretty con
	pretty (Tuple expList) = parenList . map pretty $ expList
-- 	-- weird stuff
	pretty (Paren e) = parens . pretty $ e
	pretty (LeftSection e op) = parens (pretty e <+> pretty op)
	pretty (RightSection op e) = parens (pretty op <+> pretty e)
-- 	-- patterns
-- 	-- special case that would otherwise be buggy
-- 	pretty (HsAsPat name (HsIrrPat e)) =
-- 		myFsep [pretty name <> char '@', char '~' <> pretty e]
-- 	pretty (HsAsPat name e) = hcat [pretty name, char '@', pretty e]
-- 	pretty HsWildCard = char '_'
	-- Lists
	pretty (List list) =
		bracketList . punctuate comma . map pretty $ list
	pretty (EnumFromTo from to) =
		bracketList [pretty from, text "..", pretty to]
	pretty (EnumFromThenTo from thenE to) =
		bracketList [pretty from <> comma, pretty thenE,
			     text "..", pretty to]
	pretty (Coerc _pos e ty) =
		myFsep [pretty e, text ":", pretty ty]
--  QP :: Quantifier -> [Pat p] -> Prop p -> Prop p
	pretty (QP quant patList body)
		= myFsep $ pretty quant : map pretty patList ++ [text ",", pretty body]


instance Pretty (NAME p) => Pretty (Con p) where
	pretty (UserCon name)    = pretty name
	pretty (BuiltinCon bcon) = pretty bcon
	

instance Pretty BuiltinCon where
	pretty UnitCon  = text "()"
	pretty FalseCon = text "False"
	pretty TrueCon  = text "True"
	pretty NilCon   = text "[]"
	pretty ConsCon  = text "::"

instance Pretty Op where
	pretty (BoolOp bop) = pretty bop
	pretty (IntOp iop)  = pretty iop
	pretty (ConOp cop)  = pretty cop

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

instance Pretty Quantifier where
	pretty ForallQ = text "forall"
	pretty ExistsQ = text "exists"

-- ------------------------- Patterns -----------------------------

instance (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => Pretty (Pat p) where
	prettyPrec _ (VarPat var) = pretty var
	prettyPrec _ (LitPat lit) = pretty lit
	prettyPrec p (InfixPat a cop b) = parensIf (p > 0) $
		myFsep [pretty a, pretty cop, pretty b]
	prettyPrec p (ConPat con []) = pretty con
	prettyPrec p (ConPat con ps) = parensIf (p > 1) $
		myFsep (pretty con : map pretty ps)
	prettyPrec _ (TuplePat ps) = parenList . map pretty $ ps
	prettyPrec _ (ListPat ps) =
		bracketList . punctuate comma . map pretty $ ps
	prettyPrec _ (ParenPat p) = parens . pretty $ p
	-- special case that would otherwise be buggy
	prettyPrec _ (AsPat var pat) =
		hcat [pretty var, char '@', pretty pat]
	prettyPrec _ WildPat = char '_'
	prettyPrec _ (SigPat pat ty) =
		myFsep [pretty pat, text ":", pretty ty]


-- ------------------------- Case bodies  -------------------------
instance (Pretty (VAR p), Pretty (TyVAR p), Pretty(GoalNAME p)) => Pretty (Alt p) where
	pretty (Alt _pos pat rhs) =
		myFsep [pretty pat, ppRhs CaseAlt rhs]		-- is this pretty printed correctly ?


-- ------------------------- Names -------------------------

instance Pretty OccName where
	pretty = text . occString

instance Pretty Name where
	pretty = pretty . nameOcc

instance Pretty (Var p) where
	pretty = pretty . varName

instance Pretty TyVar where
	pretty = pretty . tyVarName

------------------------- pp utils -------------------------
maybePP :: (a -> Doc) -> Maybe a -> Doc
maybePP _ Nothing = empty
maybePP pp (Just a) = pp a

parenList :: [Doc] -> Doc
parenList = parens . myFsepSimple . punctuate comma

braceList :: [Doc] -> Doc
braceList = braces . myFsepSimple . punctuate comma

bracketList :: [Doc] -> Doc
bracketList = brackets . myFsepSimple

-- Wrap in braces and semicolons, with an extra space at the start in
-- case the first doc begins with "-", which would be scanned as {-
flatBlock :: [Doc] -> Doc
flatBlock = braces . (space <>) . hsep . punctuate semi

-- Same, but put each thing on a separate line
prettyBlock :: [Doc] -> Doc
prettyBlock = braces . (space <>) . vcat . punctuate semi

-- Monadic PP Combinators -- these examine the env

blankline :: Doc -> Doc
blankline dl = do{e<-getPPEnv;if spacing e && layout e /= PPNoLayout
			      then space $$ dl else dl}
topLevel :: Doc -> [Doc] -> Doc
topLevel header dl = do
	 e <- fmap layout getPPEnv
	 case e of
	     PPOffsideRule -> header $$ vcat dl
	     PPSemiColon -> header $$ prettyBlock dl
	     PPInLine -> header $$ prettyBlock dl
	     PPNoLayout -> header <+> flatBlock dl

ppBody :: (PPHsMode -> Int) -> [Doc] -> Doc
ppBody f dl = do
	e <- fmap layout getPPEnv
	i <- fmap f getPPEnv
	case e of
	    PPOffsideRule -> nest i . vcat $ dl
	    PPSemiColon   -> nest i . prettyBlock $ dl
	    _             -> flatBlock dl

ppBindings :: [Doc] -> Doc
ppBindings dl = do
	e <- fmap layout getPPEnv
	case e of
	    PPOffsideRule -> vcat dl
	    PPSemiColon   -> vcat . punctuate semi $ dl
	    _             -> hsep . punctuate semi $ dl

($$$) :: Doc -> Doc -> Doc
a $$$ b = layoutChoice (a $$) (a <+>) b

mySep :: [Doc] -> Doc
mySep = layoutChoice mySep' hsep
	where
	-- ensure paragraph fills with indentation.
	mySep' [x]    = x
	mySep' (x:xs) = x <+> fsep xs
	mySep' []     = error "Internal error: mySep"

myVcat :: [Doc] -> Doc
myVcat = layoutChoice vcat hsep

myFsepSimple :: [Doc] -> Doc
myFsepSimple = layoutChoice fsep hsep

-- same, except that continuation lines are indented,
-- which is necessary to avoid triggering the offside rule.
myFsep :: [Doc] -> Doc
myFsep = layoutChoice fsep' hsep
	where	fsep' [] = empty
		fsep' (d:ds) = do
			e <- getPPEnv
			let n = onsideIndent e
			nest n (fsep (nest (-n) d:ds))

layoutChoice :: (a -> Doc) -> (a -> Doc) -> a -> Doc
layoutChoice a b dl = do e <- getPPEnv
                         if layout e == PPOffsideRule ||
                            layout e == PPSemiColon
                          then a dl else b dl

-- Prefix something with a LINE pragma, if requested.
-- GHC's LINE pragma actually sets the current line number to n-1, so
-- that the following line is line n.  But if there's no newline before
-- the line we're talking about, we need to compensate by adding 1.

markLine :: SrcLoc -> Doc -> Doc
markLine loc doc = do
	e <- getPPEnv
	let y = srcLine loc
	let line l =
	      text ("{-# LINE " ++ show l ++ " \"" ++ srcFilename loc ++ "\" #-}")
	if linePragmas e then layoutChoice (line y $$) (line (y+1) <+>) doc
	      else doc
