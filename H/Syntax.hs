{-# LANGUAGE GADTs,
             TypeOperators,
             EmptyDataDecls,
             MultiParamTypeClasses,
             FlexibleInstances,
             FlexibleContexts,
             RankNTypes,
             TypeFamilies
             #-}

-- | Syntax of H!
module H.Syntax
  where

import H.Phase
import H.SrcLoc

import Name
import Sorted
import Unique( Uniq, Uniquable(..), MonadUnique(..) )

import Data.STRef( STRef )
import Data.Function ( on )



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


  -- | Essentially a kinded 'Name'
data TyVar = TyV {
               tyVarName   :: !Name
             , tyVarKind   :: !Kind
             , skolemTyVar :: !Bool
                -- ^ Is it a skolem type variable ?
             }

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

-- ** Instantiate variables

instTyVar :: MonadUnique m => TyVar -> m TyVar
instTyVar (TyV name kind False) = do name' <- newNameFrom name
                                     return (TyV name' kind True)
instTyVar _other                = undefined

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

type TyNAME phase = TyVAR phase

type family GoalNAME phase
type instance GoalNAME Pr = OccName
type instance GoalNAME Rn = Name
type instance GoalNAME Tc = Name
type instance GoalNAME Ti = Name
type instance GoalNAME Vc = Name

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

data Module p where
  Module :: SrcLoc -> ModuleName -> [AnyDecl p] -> Module p

newtype ModuleName = ModName String


-- * Declarations

-- | Sort of type declarations
data Ty
-- | Sort of function and type signatures declarations
data Fn
-- | Sort of logical goals
data Lg

  -- | Any kind of declaration
data AnyDecl p = forall s. AnyDecl (Decl s p)

data Decl s p where
  -- | type synonym 
  TypeDecl ::	SrcLoc -> TyNAME p -> TyParams p -> Type p -> Decl Ty p
  -- | inductive data type
  DataDecl ::	SrcLoc -> TyNAME p -> TyParams p -> [ConDecl p] -> Decl Ty p
  -- | type signature(s)
  TypeSig :: SrcLoc -> [NAME p] -> PolyType p -> Decl Fn p
  -- | a function defined by a *set* of equations
  -- NB: Only uniform definitions are allowed
  FunBind :: IsRec p -> NAME p -> [Match p] -> Decl Fn p
  -- | pattern binding
  PatBind :: SrcLoc -> IsRec p -> Pat p -> Rhs p -> Decl Fn p
  -- | logical goal: a theorem or a lemma
  GoalDecl :: SrcLoc -> GoalType -> GoalNAME p
            -> PostTcTyParams p
              -- ^ if a goal depends on some arbitrary type
              -- that is inferred during type checking;
              -- note that the logical 'forall' does not allow
              -- to quantify over types.
            -> Prop p -> Decl Lg p

type WhereDecls p = [Decl Fn p]

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
  Let :: [Decl Fn p] -> Exp p -> Exp p
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

-- ** Right-hand side

-- | The right hand side of a function or pattern binding.
data Rhs p = Rhs (GRhs p) (WhereDecls p)

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

-- | An /alt/ in a @case@ expression.
data Alt p = Alt SrcLoc (Pat p) (Rhs p)

-- ** Literals

data Lit = IntLit Integer
    deriving Eq

-- ** Data constructors

data Con p = UserCon (NAME p)
           | BuiltinCon BuiltinCon

data BuiltinCon = UnitCon
                | FalseCon
                | TrueCon
                | NilCon
                | ConsCon
    deriving(Eq,Ord)

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

-- ** Logical quantifiers

data Quantifier = ForallQ
                | ExistsQ
    deriving Eq


-- * Types

typeOf :: Sorted a (Type p) => a -> Type p
typeOf = sortOf

-- | Rank-1 polymorphic types
data PolyType p = ForallTy (TyParams p) (Type p)

-- | Monomorphic types
data Type p where
  -- | type variable
  VarTy :: TyVAR p -> Type p
  -- | named type or type constructor
  ConTy :: TyCon p -> Type p
  -- | application of a type constructor
  AppTy :: Type p -> Type p -> Type p
  -- | subset type
  PredTy :: Pat p -> Type p -> Maybe (Prop p) -> Type p
  -- | function type
  FunTyIn :: Type Pr -> Range Pr -> Type Pr
  FunTy :: Ge p Rn => Dom p -> Range p -> Type p
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
dom2type (Dom mbPat ty mbProp) = PredTy pat ty mbProp
  where pat = maybe WildPat id mbPat

type Range = Type

type PostTcType p = PostTc p (Type p)

-- ** Type constructors

data TyCon p = UserTyCon (TyNAME p)
             | BuiltinTyCon BuiltinTyCon

data BuiltinTyCon = UnitTyCon
                  | BoolTyCon
                  | IntTyCon
                  | NatTyCon    -- ^ @{n:Int|n >= 0}@
    deriving Eq

unitTyCon, boolTyCon, intTyCon, natTyCon :: TyCon p
unitTyCon = BuiltinTyCon UnitTyCon
boolTyCon = BuiltinTyCon BoolTyCon
intTyCon  = BuiltinTyCon IntTyCon
natTyCon  = BuiltinTyCon NatTyCon

instance Sorted BuiltinTyCon Kind where
  sortOf UnitTyCon = typeKi
  sortOf BoolTyCon = typeKi
  sortOf IntTyCon  = typeKi
  sortOf NatTyCon  = typeKi

-- ** Meta type variables

data MetaTyVar = MetaTyV {
                   mtvUniq :: !Uniq
                 , mtvKind :: !Kind
                 , mtvRef  :: forall s. STRef s (Maybe (Type Tc))
                 }

-- ** Constructors

(\-->) :: Ge p Rn => Dom p -> Range p -> Type p
(\-->) = FunTy

(-->) :: Ge p Rn => Type p -> Type p -> Type p
dom --> ran = Dom Nothing dom Nothing \--> ran

unitTy, boolTy, intTy, natTy :: Type p
unitTy = ConTy unitTyCon
boolTy = ConTy boolTyCon
intTy  = ConTy intTyCon
natTy  = ConTy natTyCon


-- * Kinds

kindOf :: Sorted a Kind => a -> Kind
kindOf = sortOf

data Kind = TypeKi
          | FunKi Kind Kind
    deriving Eq

type PostTcKind p = PostTc p Kind

-- ** Constructors

typeKi :: Kind
typeKi = TypeKi

(++>) :: Kind -> Kind -> Kind
(++>) = FunKi
