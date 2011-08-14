{-# LANGUAGE GADTs,
             TypeOperators,
             EmptyDataDecls,
             MultiParamTypeClasses,
             FlexibleInstances,
             FlexibleContexts,
             RankNTypes,
             TypeFamilies,
             UndecidableInstances,
             StandaloneDeriving
             #-}

-- | Syntax of H!
module H.Syntax
  where

import H.Phase
import H.Pretty
import H.SrcLoc

import Name
import Sorted
import Unique( Uniq, Uniquable(..), MonadUnique(..) )

import Data.IORef( IORef, newIORef )
import Data.Function ( on )
import Control.Monad ( liftM )
import Control.Monad.IO.Class ( MonadIO(..) )



-- * Variables

  -- | A typed 'Name'
data Var p = V {
               varName :: !Name
             , varType :: PolyType p
             }

instance Eq (Var p) where
  (==) = (==) `on` varName

instance Ord (Var p) where
  compare = compare `on` varName

instance Named (Var p) where
  nameOf = varName

instance Uniquable (Var p) where
  uniqOf = uniqOf . nameOf

instance Sorted (Var p) (PolyType p) where
  sortOf = varType

instance Pretty (Var p) where
  pretty = pretty . varName


  -- | Essentially a kinded 'Name'
data TyVar = TyV {
               tyVarName   :: !Name
             , tyVarKind   :: !Kind
             , skolemTyVar :: !Bool
                -- ^ Is it a skolem type variable ?
             }

mkTyVar :: Name -> Kind -> TyVar
mkTyVar nm ki = TyV nm ki False

instance Eq TyVar where
  (==) = (==) `on` tyVarName

instance Ord TyVar where
  compare = compare `on` tyVarName

instance Named TyVar where
  nameOf = tyVarName

instance Uniquable TyVar where
  uniqOf = uniqOf . nameOf

instance Sorted TyVar Kind where
  sortOf = tyVarKind

instance Pretty TyVar where
  pretty = pretty . tyVarName

-- ** Fresh variables

newVar :: MonadUnique m => String -> PolyType p -> m (Var p)
newVar str ty = do name <- newName VarNS str
                   return $ V name ty

newVarFrom :: MonadUnique m => Var p -> m (Var p)
newVarFrom (V name ty) = do name' <- newNameFrom name
                            return $ V name' ty

newTyVar :: MonadUnique m => String -> Kind -> m TyVar
newTyVar str ki = do name <- newName TyVarNS str
                     return $ TyV name ki False

newTyVarFrom :: MonadUnique m => TyVar -> m TyVar
newTyVarFrom (TyV name ki isSk) = do
  name' <- newNameFrom name
  return $ TyV name' ki isSk

-- ** Skolemise variables

skoTyVar :: MonadUnique m => TyVar -> m TyVar
skoTyVar (TyV name kind False) = do
  name' <- newNameFrom name
  return (TyV name' kind True)
skoTyVar _other                = undefined

-- ** Name/Variable type per compilation phase

type family VAR phase
type instance VAR Pr = OccName
type instance VAR Rn = Name
type instance VAR Tc = Var Tc
type instance VAR Ti = Var Ti
type instance VAR Vc = Var Vc

type NAME phase = VAR phase

type family TyVAR phase
type instance TyVAR Pr = OccName
type instance TyVAR Rn = Name
type instance TyVAR Tc = TyVar
type instance TyVAR Ti = TyVar
type instance TyVAR Vc = TyVar

type UTyNAME phase = TyVAR phase

type family TyCON phase
type instance TyCON Pr = TyName Pr
type instance TyCON Rn = TyName Rn
type instance TyCON Tc = TyCon Tc

type family GoalNAME phase
type instance GoalNAME Pr = OccName
type instance GoalNAME Rn = Name
type instance GoalNAME Tc = Name
type instance GoalNAME Ti = Name
type instance GoalNAME Vc = Name


class (Pretty (VAR p), Pretty (TyVAR p), Pretty (TyCON p), Pretty(GoalNAME p)) => PrettyNames p where
instance PrettyNames Pr where
instance PrettyNames Rn where

-- ** Parameters

type Params p = [Pat p]

{- NOTE [Params]
A pattern cannot capture predicate-types during type inference
  e.g. in (x::xs) : {l:[Int]| P l}
       the inferred type for x::xs is [Int]
but a trivial workaround is to use a @-pattern
  e.g. in l@(x::xs) : {l:[Int]| P l}
       the inferred type for l@(x::xs) is {l:[Int]| P l}
-}

  -- Only type parameters of kind 'type' are supported
  -- so any kind annotation is pointless.
type TyParams p = [TyVAR p]

type PostTcTyParams p = PostTc p [TyVar]


-- * Modules

data Module p = Module SrcLoc ModuleName [Decl p]


newtype ModuleName = ModName String


instance PrettyNames p => Pretty (Module p) where
  pretty (Module pos modName decls) =
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

data Decl p where
  -- | type synonym 
  TypeDecl ::	SrcLoc -> UTyNAME p -> TyParams p -> Type p -> Decl p
  -- | inductive data type
  DataDecl ::	SrcLoc -> UTyNAME p -> TyParams p -> [ConDecl p] -> Decl p
--   -- | type signature
--   TypeSig :: SrcLoc -> NAME Pr -> PolyType Pr -> Decl Pr
  -- | Value declarations
  ValDecl :: Bind p -> Decl p
  -- | logical goal: a theorem or a lemma
  GoalDecl :: SrcLoc -> GoalType -> GoalNAME p
            -> PostTcTyParams p
              -- ^ if a goal depends on some arbitrary type
              -- that is inferred during type checking;
              -- note that the logical 'forall' does not allow
              -- to quantify over types.
            -> Prop p -> Decl p


data Bind p = FunBind (IsRec p) (NAME p) (TypeSig p) [Match p]
                  -- ^ a function defined by a *set* of equations
                  -- NB: Only uniform definitions are allowed
                  -- NB: @f = ...@ is considered a FunBind because that allows
                  --     the annotation with a polymorphic type.
            | PatBind SrcLoc (Pat p) (Rhs p)
                  -- ^ pattern binding

data TypeSig p = NoTypeSig
               | TypeSig SrcLoc (PolyType p)

type WhereBinds p = [Bind p]

  -- Everything is parsed as potentially recursive and later
  -- we perform an analysis to detect non-recursive definitions.
data IsRec p where
  -- | recursive
  Rec :: IsRec p
  -- | non-recursive 
  NonRec :: Lt Pr p => IsRec p

-- | Declaration of a data constructor.
data ConDecl p where
  ConDeclIn :: SrcLoc -> NAME Pr -> [Type Pr] -> ConDecl Pr
  ConDecl :: Ge p Rn => SrcLoc -> NAME p -> [Dom p] -> ConDecl p

-- | Clauses of a function binding.
data Match p
	 = Match SrcLoc [Pat p] (Rhs p)

data GoalType = TheoremGoal
              | LemmaGoal
  deriving Eq


instance PrettyNames p => Pretty (Decl p) where
  pretty (TypeDecl loc name nameList htype) =
    blankline $
    mySep ( [text "type", pretty name]
      ++ map pretty nameList
      ++ [equals, pretty htype])
  pretty (DataDecl loc name nameList constrList) =
    blankline $
    mySep ( [text "data", pretty name]
      ++ map pretty nameList)
      <+> myVcat (zipWith (<+>) (equals : repeat (char '|'))
               (map pretty constrList))
--   pretty (TypeSig pos name polyType)
--     = blankline $
--       mySep [pretty name, text ":", pretty polyType]
  pretty (ValDecl bind) = blankline $ pretty bind
  pretty (GoalDecl pos goaltype gname _ptctys prop)
    = blankline $
        myFsep [pretty goaltype, pretty gname, equals, pretty prop]

instance Pretty GoalType where
  pretty TheoremGoal = text "theorem"
  pretty LemmaGoal   = text "lemma"

instance PrettyNames p => Pretty (Bind p) where
  pretty (FunBind _rec fun sig matches) =
         ppTypeSig fun sig
      $$ ppBindings (map (ppMatch fun) matches)
  pretty (PatBind pos pat (Rhs grhs whereDecls)) =
    myFsep [pretty pat, ppGRhs ValDef grhs]
        $$$ ppWhere whereDecls

ppTypeSig :: PrettyNames p => NAME p -> TypeSig p -> Doc
ppTypeSig _fun NoTypeSig = empty
ppTypeSig  fun (TypeSig _loc polyty) = mySep [pretty fun, text ":", pretty polyty]

ppMatch :: PrettyNames p => NAME p -> Match p -> Doc
ppMatch fun (Match pos ps (Rhs grhs whereDecls)) =
    myFsep (lhs ++ [ppGRhs ValDef grhs])
    $$$ ppWhere whereDecls
      where
    lhs = pretty fun : map (prettyPrec 2) ps

ppWhere :: PrettyNames p => WhereBinds p -> Doc
ppWhere [] = empty
ppWhere l  = nest 2 (text "where" $$$ ppBody whereIndent (map pretty l))

instance PrettyNames p => Pretty (ConDecl p) where
  pretty (ConDeclIn _pos name typeList) =
    mySep $ pretty name : map (prettyPrec prec_atype) typeList
  pretty (ConDecl _pos name typeList) =
    mySep $ pretty name : map (prettyPrec prec_atype) typeList


-- * Expressions

data Exp p where
  -- | variable
  Var :: VAR p -> Exp p
  -- | data constructor
  Con :: Con p -> Exp p
  -- | literal constant
  Lit :: Lit -> Exp p
  -- | @else@ guard expression
  -- It is used to facilitate parsing but then removed during renaming
  ElseGuard :: Exp Pr
  -- | prefix application
  PrefixApp :: Op -> Exp p -> Exp p
  -- | infix application
  InfixApp :: Exp p -> Op -> Exp p -> Exp p
  -- | application
  App :: Exp p -> Exp p -> Exp p
  -- | type application
  TyApp :: Ge p Tc => Exp p -> [Type p] -> Exp p
  -- | lambda expression
  Lam :: SrcLoc -> [Pat p] -> Exp p -> Exp p
  -- | local declarations with @let@
  Let :: [Bind p] -> Exp p -> Exp p
  -- | type lambda
  TyLam :: Ge p Tc => [TyVar] -> Exp p -> Exp p
  -- | @if@ /exp/ @then@ /exp/ @else@ /exp/
  Ite :: Prop p -> Exp p -> Exp p -> Exp p
  -- | Generalized @if@ expressions
  If :: GuardedRhss p -> Exp p
  -- | @case@ /exp/ @of@ /alts/
  Case :: Exp p
        -> PostTcType p
            -- ^ the type of the whole case expression
        -> [Alt p] -> Exp p
  -- | tuple expression
  Tuple :: [Exp p] -> Exp p
  -- | list expression
  List :: [Exp p] -> Exp p
  -- | parenthesized expression
  Paren :: Exp p -> Exp p
  -- | left section @(@/exp/ /qop/@)@
  LeftSection :: Exp p -> Op -> Exp p
  -- | right section @(@/qop/ /exp/@)@
  RightSection :: Op -> Exp p -> Exp p
  -- | bounded arithmetic sequence, incrementing by 1
  EnumFromTo :: Exp p -> Exp p -> Exp p
  -- ^ bounded arithmetic sequence, with first two elements given
  EnumFromThenTo :: Exp p -> Exp p -> Exp p -> Exp p
  -- | explicit type coercion
  Coerc :: SrcLoc -> Exp p -> PolyType p -> Exp p
  -- | logic quantifier
  QP :: Quantifier -> [Pat p] -> Prop p -> Prop p

-- | Expressions of boolean type
type Prop = Exp

isElseGuard :: Exp Pr -> Bool
isElseGuard ElseGuard = True
isElseGuard _other    = False

instance PrettyNames p => Pretty (Exp p) where
  pretty (Lit lit) = pretty lit
  pretty ElseGuard = text "else"
  pretty (PrefixApp op a) = myFsep [pretty op, pretty a]
  pretty (InfixApp a op b) = myFsep [pretty a, pretty op, pretty b]
  pretty (App a b) = myFsep [pretty a, pretty b]
  pretty (Lam _loc patList body) = myFsep $
    char '\\' : map pretty patList ++ [text "->", pretty body]
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
  pretty (Paren e) = parens . pretty $ e
  pretty (LeftSection e op) = parens (pretty e <+> pretty op)
  pretty (RightSection op e) = parens (pretty op <+> pretty e)
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
  pretty (QP quant patList body)
    = myFsep $ pretty quant : map pretty patList ++ [text ",", pretty body]

-- ** Right-hand side

-- | The right hand side of a function or pattern binding.
data Rhs p = Rhs (GRhs p) (WhereBinds p)

data GRhs p
	 = UnGuarded (Exp p)	-- ^ unguarded right hand side (/exp/)
	 | Guarded (GuardedRhss p)
				-- ^ guarded right hand side (/gdrhs/)
        -- See [Guards]

data GuardedRhss p where
  GuardedRhssIn :: [GuardedRhs Pr] -> GuardedRhss Pr
  GuardedRhss :: Ge p Rn => [GuardedRhs p] -> Else p -> GuardedRhss p

-- | A guarded right hand side @|@ /exp/ @=@ /exp/ or @|@ /exp/ @->@ /exp/.
-- The first expression is boolean-valued.
data GuardedRhs p
	 = GuardedRhs SrcLoc (Prop p) (Exp p)

-- | @else@ clause
data Else p where
  Else   :: Ge p Rn => SrcLoc -> Exp p -> Else p
  NoElse :: Ge p Rn => Else p

{- [Guards]
In H! guarded expressions are more restricted than in Haskell.
First, a set of guards has to be exhaustive, which may cause the
generation of a coverage TCC. This TCC is omitted if there is an
'else' clause.
Second, guards cannot overlap which will lead to the generation of the
corresponding TCC. This may look like a kick-in-the-ass but it is
convenient when writing critical software.
-}

data RhsContext = ValDef
                | CaseAlt
                | IfExp

rhsSepSym :: RhsContext -> Doc
rhsSepSym ValDef  = equals
rhsSepSym CaseAlt = text "->"
rhsSepSym IfExp   = text "->"

ppRhs :: PrettyNames p => RhsContext -> Rhs p -> Doc
ppRhs ctx (Rhs grhs whereDecls) = ppGRhs ctx grhs $$$ ppWhere whereDecls

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
ppElse ctx (Else _pos body)
  = myFsep [char '|', text "else", rhsSepSym ctx, pretty body]
ppElse ctx  NoElse   = empty

-- ** Patterns

-- | A pattern, to be matched against a value.
data Pat p where
  -- | variable
  VarPat :: VAR p -> Pat p
  -- | literal constant
  LitPat :: Lit -> Pat p
  -- | pattern with infix data constructor
  InfixPat :: Pat p -> BuiltinCon -> Pat p -> Pat p
  -- | data constructor and argument
  ConPat :: Con p -> [Pat p] -> Pat p
  -- | tuple pattern
  TuplePat :: [Pat p] -> Pat p
  -- | list pattern
  ListPat :: [Pat p] -> Pat p
  -- | parenthesized pattern
  ParenPat :: Pat p -> Pat p
  -- | wildcard pattern (@_@)
  WildPat :: Pat p
  -- ^ as-pattern (@\@@)
  AsPat :: VAR p -> Pat p -> Pat p
  -- ^ pattern signature
    -- Add SrcLoc ?
  SigPat :: Pat p -> Type p -> Pat p

patBndrs :: Pat p -> [VAR p]
patBndrs (VarPat var) = [var]
patBndrs (LitPat _lit) = []
patBndrs (InfixPat p1 op p2) = patBndrs p1 ++ patBndrs p2
patBndrs (ConPat con ps) = patsBndrs ps
patBndrs (TuplePat ps) = patsBndrs ps
patBndrs (ListPat ps) = patsBndrs ps
patBndrs (ParenPat p) = patBndrs p
patBndrs WildPat      = []
patBndrs (AsPat v p)  = v : patBndrs p
patBndrs (SigPat p _t) = patBndrs p

patsBndrs :: [Pat p] -> [VAR p]
patsBndrs = concatMap patBndrs

-- | An /alt/ in a @case@ expression.
data Alt p = Alt SrcLoc (Pat p) (Rhs p)


instance PrettyNames p => Pretty (Pat p) where
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
    parens $ myFsep [pretty pat, text ":", pretty ty]

instance PrettyNames p => Pretty (Alt p) where
  pretty (Alt _pos pat rhs) =
    myFsep [pretty pat, ppRhs CaseAlt rhs]    -- is this pretty printed correctly ?


-- ** Literals

data Lit = IntLit Integer
    deriving Eq

instance Pretty Lit where
  pretty (IntLit i) = integer i

-- ** Data constructors

data Con p = UserCon (NAME p)
           | BuiltinCon BuiltinCon

deriving instance Eq (NAME p) => Eq (Con p)
deriving instance Ord (NAME p) => Ord (Con p)

data BuiltinCon = UnitCon
                | FalseCon
                | TrueCon
                | NilCon
                | ConsCon
    deriving(Eq,Ord)

instance (Ge p Tc, VAR p ~ Var p, TyVAR p ~ TyVar, TyCON p ~ TyCon p) => Sorted BuiltinCon (PolyType p) where
  sortOf UnitCon  = monoTy $ unitTy
  sortOf FalseCon = monoTy $ boolTy
  sortOf TrueCon  = monoTy $ boolTy
  sortOf NilCon   = ForallTy [a_tv] $ a --> ListTy a
    where a_nm = mkUsrName (mkOccName TyVarNS "a") a_uniq
          a_uniq = -1001
          a_tv = TyV a_nm typeKi False
          a = VarTy a_tv
  sortOf ConsCon  = ForallTy [a_tv] $ a --> ListTy a --> ListTy a
    where a_nm = mkUsrName (mkOccName TyVarNS "a") a_uniq
          a_uniq = -1002
          a_tv = TyV a_nm typeKi False
          a = VarTy a_tv

instance (Ge p Tc, VAR p ~ Var p, TyVAR p ~ TyVar, TyCON p ~ TyCon p) => Sorted (Con p) (PolyType p) where
  sortOf (UserCon ucon)    = sortOf ucon
  sortOf (BuiltinCon bcon) = sortOf bcon

instance Pretty (NAME p) => Pretty (Con p) where
  pretty (UserCon name)    = pretty name
  pretty (BuiltinCon bcon) = pretty bcon

instance Pretty BuiltinCon where
  pretty UnitCon  = text "()"
  pretty FalseCon = text "False"
  pretty TrueCon  = text "True"
  pretty NilCon   = text "[]"
  pretty ConsCon  = text "::"

unitCon, trueCon, falseCon, nilCon, consCon :: Con p
unitCon  = BuiltinCon UnitCon
trueCon  = BuiltinCon TrueCon
falseCon = BuiltinCon FalseCon
nilCon   = BuiltinCon NilCon
consCon  = BuiltinCon ConsCon

-- ** Built-in operators

data Op = BoolOp BoolOp
        | IntOp IntOp
        | ConOp BuiltinCon
    deriving(Eq,Ord)

-- | Operators for building boolean expressions
data BoolOp = NotB
            | OrB
            | AndB
            | ImpB
            | IffB
            | EqB   -- ^ @==@
            | NeqB  -- ^ @/=@
            | LtB
            | LeB
            | GtB
            | GeB
    deriving(Eq,Ord)

notOp, orOp, andOp, impOp, iffOp :: Op
eqOp, neqOp, ltOp, leOp, gtOp, geOp :: Op
notOp = BoolOp NotB
orOp  = BoolOp OrB
andOp = BoolOp AndB
impOp = BoolOp ImpB
iffOp = BoolOp IffB
eqOp  = BoolOp EqB
neqOp = BoolOp NeqB
ltOp  = BoolOp LtB
leOp  = BoolOp LeB
gtOp  = BoolOp GtB
geOp  = BoolOp GeB

-- | Operators for building integer expressions
data IntOp = NegI   -- ^ negation @-@ /exp/
           | AddI
           | SubI
           | MulI
           | DivI
           | ModI
           | ExpI
    deriving(Eq,Ord)

negOp, addOp, subOp, mulOp, divOp, modOp, expOp :: Op
negOp = IntOp NegI
addOp = IntOp AddI
subOp = IntOp SubI
mulOp = IntOp MulI
divOp = IntOp DivI
modOp = IntOp ModI
expOp = IntOp ExpI

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

-- ** Logical quantifiers

data Quantifier = ForallQ
                | ExistsQ
    deriving Eq

instance Pretty Quantifier where
  pretty ForallQ = text "forall"
  pretty ExistsQ = text "exists"

-- ** Constructors

(.>.), (.>=.) :: Exp p -> Exp p -> Prop p
x .>. y = InfixApp x gtOp y
x .>=. y = InfixApp x geOp y

-- * Types

typeOf :: Sorted a (Type p) => a -> Type p
typeOf = sortOf

-- | Rank-1 polymorphic types
data PolyType p = ForallTy (TyParams p) (Type p)

monoTy :: Type p -> PolyType p
monoTy = ForallTy []

-- | Monomorphic types
data Type p where
  -- | type variable
  VarTy :: TyVAR p -> Type p
  -- | named type or type constructor
  ConTyIn :: Lt p Tc => TyCON p -> Type p
  -- | application of a type constructor
  AppTyIn :: Lt p Tc => Type p -> Type p -> Type p
  ConTy :: Ge p Tc => TyCON p -> [Type p] -> Type p
  -- | subset type
  PredTy :: Pat p -> Type p -> Maybe (Prop p) -> Type p
  -- | function type
  FunTy :: Dom p -> Range p -> Type p
  -- | list type
  ListTy :: Type p -> Type p
  -- | tuple type
  TupleTy :: [Dom p] -> Type p
  -- | parenthised type
  ParenTy :: Type Pr -> Type Pr 
  -- | meta type variable
  MetaTy :: MetaTyVar -> Type Tc

  -- NB: The @Dom Nothing ty (Just prop)@ is pointless
data Dom p = Dom {
               domMbPat  :: Maybe (Pat p)
             , domType   :: Type p
             , domMbProp :: Maybe (Prop p)
             }

dom2type :: Dom p -> Type p
dom2type (Dom mbPat ty mbProp) = predTy pat ty mbProp
  where pat = maybe WildPat id mbPat

type Range = Type

type PostTcType p = PostTc p (Type p)

  -- (args,result)
splitFunTy :: Type p -> ([Type p],Type p)
splitFunTy (FunTy d t) = (a:args,res)
  where a = dom2type d
        (args,res) = splitFunTy t
splitFunTy ty = ([],ty)

-- | Removes outermost predicate-types
mu_0 :: Type p -> Type p
mu_0 (PredTy _ ty _) = mu_0 ty
mu_0 ty              = ty

isSynTy :: (Ge p Tc, VAR p ~ Var p, TyCON p ~ TyCon p) => Type p -> Bool
isSynTy (ConTy SynTyCon{} _) = True
isSynTy _other               = False


ppDomType :: PrettyNames p => Dom p -> Doc
ppDomType = prettyPrec prec_btype

ppAType :: PrettyNames p => Type p -> Doc
ppAType = prettyPrec prec_atype

-- precedences for types
prec_btype, prec_atype :: Int
prec_btype = 1  -- left argument of ->,
    -- or either argument of an infix data constructor
prec_atype = 2  -- argument of type or data constructor, or of a class

instance PrettyNames p => Pretty (PolyType p) where
  pretty (ForallTy [] ty)
    = pretty ty
  pretty (ForallTy typarams ty)
    = myFsep [text "forall", mySep $ map pretty typarams, char '.', pretty ty]

instance PrettyNames p => Pretty (Type p) where
  prettyPrec _ (PredTy pat ty Nothing)
    = braces $ mySep [pretty pat, char ':', pretty ty]
  prettyPrec _ (PredTy pat ty (Just prop))
    = braces $ mySep [pretty pat, char ':', pretty ty, char '|', pretty prop]
  prettyPrec p (FunTy a b) = parensIf (p > 0) $
    myFsep [ppDomType a, text "->", pretty b]
  prettyPrec _ (ListTy a)  = brackets $ pretty a
  prettyPrec _ (TupleTy l) = parenList . map ppTupleDom $ l
  prettyPrec p (AppTyIn a b) = parensIf (p > prec_btype) $
      myFsep [pretty a, ppAType b]
  prettyPrec p (ConTy tc args) = parensIf (p > prec_btype) $
      myFsep $ pretty tc : map ppAType args
  prettyPrec _ (VarTy name) = pretty name
  prettyPrec _ (ConTyIn tycon) = pretty tycon
  prettyPrec _ (ParenTy ty) = pretty ty
  prettyPrec _ (MetaTy mtv) = pretty mtv

instance PrettyNames p => Pretty (Dom p) where
  prettyPrec p (Dom Nothing ty Nothing) = prettyPrec p ty
  -- dependent arrow
  prettyPrec _p (Dom (Just pat) ty Nothing)
    = braces $ mySep [pretty pat, char ':', pretty ty]
  prettyPrec _p (Dom (Just pat) ty (Just prop))
    = braces $ mySep [pretty pat, char ':', pretty ty, char '|', pretty prop]
  prettyPrec _p _other = undefined

ppTupleDom :: PrettyNames p => Dom p -> Doc
ppTupleDom (Dom Nothing ty Nothing) = pretty ty
ppTupleDom (Dom (Just pat) ty Nothing)
  = mySep [pretty pat, char ':', pretty ty]
ppTupleDom (Dom (Just pat) ty (Just prop))
  = mySep [pretty pat, char ':', pretty ty, char '|', pretty prop]

-- ** Type constructors

data TyName p = UserTyCon (UTyNAME p)
              | BuiltinTyCon BuiltinTyCon

deriving instance Eq (UTyNAME p) => Eq (TyName p)
deriving instance Ord (UTyNAME p) => Ord (TyName p)

  -- Should I include ListTyCon ?
  -- right now list is a built-in type (not a built-in type constructor)
  -- but just because list type has special syntax and in this way
  -- pretty-printing is slightly easier.
data BuiltinTyCon = UnitTyCon
                  | BoolTyCon
                  | IntTyCon
                  | NatTyCon    -- ^ @{n:Int|n >= 0}@
    deriving (Eq,Ord)

instance Sorted (UTyNAME p) Kind => Sorted (TyName p) Kind where
  sortOf (UserTyCon utycon)    = sortOf utycon
  sortOf (BuiltinTyCon btycon) = sortOf btycon

instance Pretty (TyVAR p) => Pretty (TyName p) where
  pretty (UserTyCon name) = pretty name
  pretty (BuiltinTyCon tycon) = pretty tycon

instance Pretty BuiltinTyCon where
  pretty UnitTyCon = text "()"
  pretty BoolTyCon = text "Bool"
  pretty IntTyCon  = text "Int"
  pretty NatTyCon  = text "Nat"

data TyCon p
  = AlgTyCon {
      tyConName   :: TyName p
    , tyConParams :: [TyVar]
    }
  | SynTyCon {
      tyConName   :: TyName p
    , tyConParams :: [TyVar]
    , synTyConRhs :: Type p
    }

instance Eq (TyName p) => Eq (TyCon p) where
  (==) = (==) `on` tyConName

instance Ord (TyName p) => Ord (TyCon p) where
  compare = compare `on` tyConName

instance Sorted (TyName p) Kind => Sorted (TyCon p) Kind where
  sortOf = sortOf . tyConName

instance Pretty (TyName p) => Pretty (TyCon p) where
  pretty = pretty . tyConName

unitTyName, boolTyName, intTyName, natTyName :: TyName p
unitTyName = BuiltinTyCon UnitTyCon
boolTyName = BuiltinTyCon BoolTyCon
intTyName  = BuiltinTyCon IntTyCon
natTyName  = BuiltinTyCon NatTyCon

unitTyCon, boolTyCon, intTyCon, natTyCon :: (Ge p Tc, VAR p ~ Var p, TyCON p ~ TyCon p) => TyCon p
unitTyCon = AlgTyCon {
              tyConName   = BuiltinTyCon UnitTyCon
            , tyConParams = []
            }
boolTyCon = AlgTyCon {
              tyConName   = BuiltinTyCon BoolTyCon
            , tyConParams = []
            }
intTyCon  = AlgTyCon {
              tyConName   = BuiltinTyCon IntTyCon
            , tyConParams = []
            }
natTyCon  = SynTyCon {
              tyConName   = BuiltinTyCon NatTyCon
            , tyConParams = []
            , synTyConRhs = predTy (VarPat n) intTy (Just $ (Var n) .>=. (Lit (IntLit 0)))
            }
  where n = V n_nm (monoTy intTy)
        n_nm = mkSysName (mkOccName VarNS "n") n_uniq
        n_uniq = -2001

instance Sorted BuiltinTyCon Kind where
  sortOf UnitTyCon = typeKi
  sortOf BoolTyCon = typeKi
  sortOf IntTyCon  = typeKi
  sortOf NatTyCon  = typeKi

-- ** Meta type variables

data MetaTyVar = MetaTyV {
                    -- a 'Uniq' would suffice but a 'Name' allows
                    -- better pretty-printing.
                   mtvName :: !Name
                 , mtvKind :: !Kind
                 , mtvRef  :: IORef (Maybe (Type Tc))
                 }

instance Eq MetaTyVar where
  (==) = (==) `on` mtvName

instance Ord MetaTyVar where
  compare = compare `on` mtvName

instance Sorted MetaTyVar Kind where
  sortOf = mtvKind

instance Pretty MetaTyVar where
  pretty (MetaTyV name _ _) = char '?' <> pretty name

instTyVar :: (MonadUnique m, MonadIO m) => TyVar -> m (Type Tc)
instTyVar (TyV name kind False) = do
  name' <- newNameFrom name
  ref <- liftIO $ newIORef Nothing
  return $ MetaTy $ MetaTyV name' kind ref
instTyVar _other = undefined

newMetaTyVar :: (MonadUnique m, MonadIO m) => String -> Kind -> m MetaTyVar
newMetaTyVar str kind = do
  name <- newName TyVarNS str
  ref <- liftIO $ newIORef Nothing
  return $ MetaTyV name kind ref

newMetaTy :: (MonadUnique m, MonadIO m) => String -> Kind -> m (Type Tc)
newMetaTy str kind = liftM MetaTy $ newMetaTyVar str kind

-- ** Constructors

(\-->) :: Dom p -> Range p -> Type p
(\-->) = FunTy

(-->) :: Type p -> Type p -> Type p
dom --> ran = Dom Nothing dom Nothing \--> ran

patternTy :: Pat p -> Type p -> Type p
patternTy WildPat    ty = ty
patternTy (VarPat _) ty = ty
patternTy pat        ty = PredTy pat ty Nothing

predTy :: Pat p -> Type p -> Maybe (Prop p) -> Type p
predTy pat ty Nothing = patternTy pat ty
predTy pat ty prop    = PredTy pat ty prop

unitTy, boolTy, intTy, natTy :: (Ge p Tc, VAR p ~ Var p, TyCON p ~ TyCon p) => Type p
unitTy = ConTy unitTyCon []
boolTy = ConTy boolTyCon []
intTy  = ConTy intTyCon []
natTy  = ConTy natTyCon []


-- * Kinds

kindOf :: Sorted a Kind => a -> Kind
kindOf = sortOf

data Kind = TypeKi
          | FunKi Kind Kind
    deriving Eq

type PostTcKind p = PostTc p Kind


instance Pretty Kind where
  prettyPrec _ TypeKi = char '*'
  prettyPrec p (FunKi k1 k2)
    = parensIf (p > 0) $
        myFsep [prettyPrec 1 k1, text "->", pretty k2]

-- ** Constructors

typeKi :: Kind
typeKi = TypeKi

(++>) :: Kind -> Kind -> Kind
(++>) = FunKi
