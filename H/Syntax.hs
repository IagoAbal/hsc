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

import Name
import Sorted
import Unique( Uniq, Uniquable(..), MonadUnique(..) )

import Data.STRef( STRef )
import Data.Function ( on )


-- * Source locations

-- | A position in the source
data SrcLoc = SrcLoc {
      srcFilename :: String
		, srcLine     :: Int
    , srcColumn   :: Int
		}
    deriving(Eq,Ord)


-- * Variables

data Var = V {
             varName :: !Name
           , varType :: PolyType Tc
           }

instance Eq Var where
  (==) = (==) `on` varName

instance Ord Var where
  compare = compare `on` varName

instance Named Var where
  nameOf = varName

instance Uniquable Var where
  uniqOf = uniqOf . nameOf

instance Sorted Var (PolyType Tc) where
  sortOf = varType


data TyVar = TyV {
               tyVarName   :: !Name
             , tyVarKind   :: !Kind
             , skolemTyVar :: !Bool
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

newVar :: MonadUnique m => String -> PolyType Tc -> m Var
newVar str ty = do name <- newName VarNS str
                   return $ V name ty

newVarFrom :: MonadUnique m => Var -> m Var
newVarFrom (V name ty) = do name' <- newNameFrom name
                            return $ V name' ty

-- ** Instantiate variables

instTyVar :: MonadUnique m => TyVar -> m TyVar
instTyVar (TyV name kind False) = do name' <- newNameFrom name
                                     return (TyV name' kind True)
instTyVar _other                = undefined

-- ** Name/Variable type per compilation phase

type family VAR phase
type instance VAR Pr = OccName
type instance VAR Rn = Name
type instance VAR Tc = Var

type NAME phase = VAR phase

type family TyVAR phase
type instance TyVAR Pr = OccName
type instance TyVAR Rn = Name
type instance TyVAR Tc = TyVar

type TyNAME phase = TyVAR phase

-- ** Type parameters

  -- The user can provide a kind annotation,
  -- if not, we will assume the 'type' kind.
type TyParams p = [TyVAR p ::: Maybe Kind]

type PostTcTyParams p = PostTc p [TyVar]


-- * Declarations

-- | Sort of type declarations
data Ty
-- | Sort of function and type signatures declarations
data Fn
-- | Sort of logical goals
data Lg

data IsRec = Rec    -- ^ recursive
           | NonRec -- ^ non-recursive 

data Decl s p where
  -- | type synonym 
  TypeDecl ::	SrcLoc -> TyNAME p -> TyParams p -> Type p -> Decl Ty p
  -- | inductive data type
  DataDecl ::	SrcLoc -> TyNAME p -> TyParams p -> [ConDecl p] -> Decl Ty p
  -- | type signature(s)
  TypeSig :: SrcLoc -> [NAME p] -> PolyType p -> Decl Fn p
  -- | a function defined by a *set* of equations
  -- NB: Only uniform definitions are allowed
  FunBind :: IsRec -> [Match p] -> Decl Fn p
  -- | pattern binding
  PatBind :: SrcLoc -> IsRec -> Pat p -> PostTcType p -> Rhs p -> WhereDecls p -> Decl Fn p
  -- | logical goal: a theorem or a lemma
  GoalDecl :: SrcLoc -> NAME p -> GoalType -> PostTcTyParams p -> Prop p -> Decl Lg p

type WhereDecls p = [Decl Fn p]

-- | Declaration of a data constructor.
data ConDecl p
	 = ConDecl SrcLoc (NAME p) [Type p]

-- | Clauses of a function binding.
data Match p
	 = Match SrcLoc (NAME p) [Pat p] (Rhs p) (WhereDecls p)

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
  -- | prefix application
  PrefixApp :: Op -> Exp p -> Exp p
  -- | infix application
  InfixApp :: Exp p -> Op -> Exp p -> Exp p
  -- | application
  App :: Exp p -> Exp p -> Exp p
  -- | type application
  TyApp :: Exp Tc -> [Type Tc] -> Exp Tc
  -- | lambda expression
  Lam :: SrcLoc
        -> [Pat p ::: PostTcType p]
            -- ^ A predicate type cannot be inferred from a pattern,
            -- so we may need a PostTcType annotation.
        -> Exp p -> Exp p
  -- | local declarations with @let@
  Let :: [Decl Fn p] -> Exp p -> Exp p
  -- | type lambda
  TyLam :: [TyVar] -> Exp Tc -> Exp Tc
  -- | @if@ /exp/ @then@ /exp/ @else@ /exp/
  If :: Prop p -> Exp p -> Exp p -> Exp p
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
  -- | type annotation
  Ann :: SrcLoc -> Exp p -> Type p -> Exp p
  -- | logic quantifier
  QP :: Quantifier -> [Pat p] -> Prop p -> Prop p

-- | Expressions of boolean type
type Prop = Exp

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
    deriving Eq

-- ** Built-in operators

data Op = BoolOp BoolOp
        | IntOp IntOp
    deriving Eq

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
    deriving Eq

-- | Operators for building integer expressions
data IntOp = NegI   -- ^ negation @-@ /exp/
           | AddI
           | SubI
           | MulI
           | DivI
           | ModI
           | ExpI
    deriving Eq

-- ** Logical quantifiers

data Quantifier = ForallQ
                | ExistsQ
    deriving Eq

-- ** Right-hand side

-- | The right hand side of a function or pattern binding.
data Rhs p
	 = UnGuardedRhs (Exp p)	-- ^ unguarded right hand side (/exp/)
	 | GuardedRhss  [GuardedRhs p] (Otherwise p)
				-- ^ guarded right hand side (/gdrhs/)
        -- See [Guards]

data Otherwise p = Otherwise (Exp p)
                 | NoOtherwise

-- | A guarded right hand side @|@ /exp/ @=@ /exp/.
-- The first expression will be Boolean-valued.
data GuardedRhs p
	 = GuardedRhs SrcLoc (Prop p) (Exp p)

{- [Guards]
In H! guarded expressions are more restricted than in Haskell.
First, a set of guards has to be exhaustive, which may cause the
generation of a coverage TCC. This TCC is omitted if there is an
'otherwise' alternative.
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

-- | An /alt/ in a @case@ expression.
data Alt p
	= Alt SrcLoc (Pat p) (Rhs p)


-- * Types

typeOf :: Sorted a (Type p) => a -> Type p
typeOf = sortOf

data PolyType p = ForallTy (TyParams p) (Type p)

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
  FunTy :: Dom p -> Range p -> Type p
  -- | tuple type
  TupleTy :: !Int -> [Dom p] -> Type p
  -- | meta type variable
  MetaTy :: MetaTyVar -> Type Tc

data Dom p = Dom (Maybe (Pat p)) (Type p) (Maybe (Prop p))

domType :: Dom p -> Type p
domType (Dom mbPat ty mbProp) = PredTy pat ty mbProp
  where pat = maybe WildPat id mbPat

type Range = Type

type PostTcType p = PostTc p (Type p)

-- ** Type constructors

data TyCon p = UserTyCon (NAME p)
             | BuiltinTyCon BuiltinType

data BuiltinType = UnitTy
                 | BoolTy
                 | IntTy
                 | NatTy    -- ^ @{n:Int|n >= 0}@
                 | ListTy
    deriving Eq

instance Sorted BuiltinType Kind where
  sortOf UnitTy = typeKi
  sortOf BoolTy = typeKi
  sortOf IntTy  = typeKi
  sortOf NatTy  = typeKi
  sortOf ListTy = typeKi ++> typeKi

-- ** Meta type variables

data MetaTyVar = MetaTyV {
                   mtvUniq :: !Uniq
                 , mtvKind :: !Kind
                 , mtvRef  :: forall s. STRef s (Maybe (Type Tc))
                 }

-- ** Constructors

(\-->) :: Dom p -> Range p -> Type p
(\-->) = FunTy

(-->) :: Type p -> Type p -> Type p
dom --> ran = Dom Nothing dom Nothing \--> ran

unitTy :: Type p
unitTy = ConTy $ BuiltinTyCon UnitTy

boolTy :: Type p
boolTy = ConTy $ BuiltinTyCon BoolTy

intTy :: Type p
intTy = ConTy $ BuiltinTyCon IntTy

natTy :: Type p
natTy = ConTy $ BuiltinTyCon NatTy

listTyCon :: Type p
listTyCon = ConTy $ BuiltinTyCon ListTy

listTy :: Type p -> Type p
listTy = AppTy listTyCon


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
