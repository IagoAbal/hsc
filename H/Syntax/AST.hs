
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      :  H.Syntax.AST
-- Copyright   :  (c) Iago Abal 2011-2012
-- License     :  BSD3
--
-- Maintainer  :  Iago Abal, iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Abstract syntax of H!

-- TODO: Play with new DataKind extension
module H.Syntax.AST
  where


import H.Syntax.Phase
import H.SrcLoc

import Name
import Sorted
import Unique( Uniquable(..) )

import Data.IORef( IORef )
import Data.Function ( on )



-- * Variables and names

type family VAR phase
type instance VAR Pr = OccName
type instance VAR Rn = Name
type instance VAR Tc = Var Tc
type instance VAR Ti = Var Ti

type NAME phase = VAR phase

type family GoalNAME phase
type instance GoalNAME Pr = OccName
type instance GoalNAME Rn = Name
type instance GoalNAME Tc = Name
type instance GoalNAME Ti = Name


  -- | Term variables
  -- Essentially a typed 'Name'
data Var p = V {
               varName   :: !Name
             , varType   :: Sigma p
             , skolemVar :: !Bool
             }

instance Eq (Var p) where
  (==) = (==) `on` varName

instance Ord (Var p) where
  compare = compare `on` varName

instance Named (Var p) where
  nameOf = varName

instance Uniquable (Var p) where
  uniqOf = uniqOf . nameOf

instance Sorted (Var p) (Sigma p) where
  sortOf = varType


type family TyVAR phase
type instance TyVAR Pr = OccName
type instance TyVAR Rn = Name
type instance TyVAR Tc = TyVar
type instance TyVAR Ti = TyVar

type UTyNAME phase = TyVAR phase


  -- | Type variables
  -- Essentially a kinded 'Name'
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


-- * Parameters

type Params p = [Pat p]

{- NOTE [Params]
A pattern cannot capture predicate-types during type inference
  e.g. in (x::xs) : {l:[Int]| P l}
       the inferred type for x::xs is [Int]
but a trivial workaround is to use a @-pattern
  e.g. in l@(x::xs) : {l:[Int]| P l}
       the inferred type for l@(x::xs) is {l:[Int]| P l}
-}

  -- NB: Now only type parameters of kind 'type' are supported so
  --     any kind annotation is pointless.
type TyParams p = [TyVAR p]

type PostTcTyParams p = PostTc p [TyVar]


-- * Modules

newtype ModuleName = ModName String

data Module p = Module !SrcLoc !ModuleName [Decl p]

{- Note [Modules]
For now, H! declarations are not mutually recursive. The dependencies
introduced by predicate types are potentially hard to handle. We hope to
overtake this problem in future versions.
-}


-- * Declarations

data Decl p where
  -- | Type synonym
  -- NB: You can only specify synonyms for mono-types.
  TypeDecl ::	!SrcLoc -> !(UTyNAME p) -> TyParams p -> Tau p -> Decl p
  -- | Inductive data type
  DataDecl ::	!SrcLoc -> !(UTyNAME p) -> TyParams p -> [ConDecl p] -> Decl p
  -- | Value declarations
  ValDecl :: Bind p -> Decl p
  -- | Logical goal (theorem/lemma)
  GoalDecl :: !SrcLoc -> !GoalType -> !(GoalNAME p)
            -> PostTcTyParams p
              -- ^ If a goal depends on some arbitrary types,
              -- those types will be inferred during type checking.
              -- Note that the logical quantifiers do not allow
              -- to quantify over types.
            -> Prop p -> Decl p


-- * Binds
-- In H! type signatures have to be declared just before the corresponding
-- bind.

data Bind p = FunBind !(IsRec p) !(NAME p) !(TypeSig p) (PostTcTyParams p) [Match p]
                  -- ^ A function defined by a *set* of equations
                  -- NB: Only uniform definitions are allowed, hence the order
                  --     of equations does not matter.
                  -- NB: @f = ...@ is considered a FunBind because that allows
                  --     'f' to be polymorphic.
            | PatBind !(Maybe SrcLoc) (Pat p) (Rhs p)
                  -- ^ Pattern binding
                  -- NB: These definitions cannot be polymorphic.

data TypeSig p = NoTypeSig
               | TypeSig !SrcLoc (Sigma p)

type WhereBinds p = [Bind p]

  -- Everything is parsed as potentially recursive and later
  -- we perform an analysis to detect non-recursive definitions.
data IsRec p where
  -- | recursive
  Rec :: IsRec p
  -- | non-recursive 
  NonRec :: Lt Pr p => IsRec p

-- | Declaration of a data constructor.
-- Constructor arguments are parsed as simple types and then converted
-- to @Dom@ during renaming.
data ConDecl p where
  ConDeclIn :: !SrcLoc -> !(NAME Pr) -> [Tau Pr] -> ConDecl Pr
  ConDecl :: Ge p Rn => !SrcLoc -> !(NAME p) -> [Dom p] -> ConDecl p

-- | Clauses of a function binding.
data Match p
	 = Match !(Maybe SrcLoc) [Pat p] (Rhs p)

matchArity :: Match p -> Int
matchArity (Match _ pats _) = length pats

-- | Type of a logical goal
data GoalType = TheoremGoal
              | LemmaGoal
  deriving Eq


-- * Expressions

data Exp p where
  -- | variable
  Var :: !(VAR p) -> Exp p
  -- | data constructor
  Con :: !(CON p) -> Exp p
  -- | operator
  Op  :: !Op -> Exp p
  -- | literal constant
  Lit :: !Lit -> Exp p
  -- | @else@ guard expression
  -- It is used to facilitate parsing of case expressions
  -- but then removed during renaming
  ElseGuard :: Exp Pr
  -- | prefix application
  PrefixApp :: OpExp p -> Exp p -> Exp p
  -- | infix application
  InfixApp :: Exp p -> OpExp p -> Exp p -> Exp p
  -- | application
  App :: Exp p -> Exp p -> Exp p
  -- | type application
  TyApp :: Ge p Tc => Exp p -> [Tau p] -> Exp p
  -- | lambda expression
  Lam :: !(Maybe SrcLoc) -> [Pat p] -> LamRHS p -> Exp p
  -- | local declarations with @let@
  -- NB: Mutually recursive bindings are still not supported.
  Let :: [Bind p] -> Exp p -> Exp p
  -- | type lambda
  TyLam :: Ge p Tc => [TyVar] -> Exp p -> Exp p
  -- | @if@ /exp/ @then@ /exp/ @else@ /exp/
  Ite :: PostTcType p -> Prop p -> Exp p -> Exp p -> Exp p
  -- | Generalized @if@ expressions
  If :: PostTcType p -> GuardedRhss p -> Exp p
  -- | @case@ /exp/ @of@ /alts/
  Case :: Exp p
        -> PostTcType p
            -- ^ the type of the whole case expression
        -> [Alt p] -> Exp p
  -- | tuple expression
  Tuple :: PostTcType p -> [Exp p] -> Exp p
  -- | list expression
  List :: PostTcType p -> [Exp p] -> Exp p
  -- | parenthesized expression
  -- This makes pretty-printing easier.
  Paren :: Exp p -> Exp p
  -- | left section @(@/exp/ /qop/@)@
  LeftSection :: Exp p -> OpExp p -> Exp p
  -- | right section @(@/qop/ /exp/@)@
  RightSection :: OpExp p -> Exp p -> Exp p
  -- | bounded arithmetic sequence, incrementing by 1
  EnumFromTo :: Exp p -> Exp p -> Exp p
  -- ^ bounded arithmetic sequence, with first two elements given
  EnumFromThenTo :: Exp p -> Exp p -> Exp p -> Exp p
  -- | explicit type coercion
  Coerc :: !SrcLoc -> Exp p -> Sigma p -> Exp p
  -- | logic quantifier
  QP :: !Quantifier -> [QVar p] -> Prop p -> Prop p

-- | Literals.
data Lit = IntLit Integer
    deriving Eq

-- | An /alt/ in a @case@ expression.
data Alt p = Alt !(Maybe SrcLoc) (Pat p) (Rhs p)

-- | Logical quantifiers.
data Quantifier = ForallQ   -- ^ forall
                | ExistsQ   -- ^ exists
    deriving Eq

-- | An Op or a TyApp on an Op
type OpExp = Exp

-- | Expressions of boolean type
type Prop = Exp

-- | Logically quantified variable
data QVar p = QVar {
                qVarVar :: VAR p         -- ^ the variable itself
              , qVarSig :: Maybe (Tau p) -- ^ optional type signature
              }

-- ** Right-hand side

-- | A (possibly guarded) right hand side.
-- NB: A Rhs has always a Tau type.
data Rhs p = Rhs (PostTcType p) (GRhs p) (WhereBinds p)

-- | RHS of a lamba-abstraction
-- Invariant: no guards nor `where' bindings.
type LamRHS = Rhs

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
	 = GuardedRhs !SrcLoc (Prop p) (Exp p)

-- | @else@ clause
data Else p where
  Else   :: Ge p Rn => SrcLoc -> Exp p -> Else p
  NoElse :: Ge p Rn => Else p

{- [Guards]
In H! guarded expressions are more restricted than in Haskell.

First, a set of guards has to be exhaustive, which may cause the
generation of a coverage TCC. Such TCC is not generated if there is an
'else' clause.

Second, guards cannot overlap which will lead to the generation of the
corresponding TCC. This may look like a kick-in-the-ass but it is
convenient when writing critical software.

  E.g. The following function definition

    f : Nat -> Nat
    f x | x == 0 = ...
        | x >= 0 = ...

  is not correct since @x == 0@ and @x >= 0@ are not disjoint.
-}


-- * Data constructors

type family CON phase
type instance CON Pr = Con Pr
type instance CON Rn = Con Rn
type instance CON Tc = TcCon Tc
type instance CON Ti = TcCon Ti


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


data TcCon p = TcCon {
    tcConCon :: Con p
      -- ^ the data constructor itself
  , tcConTy  :: TyCon p
      -- ^ the corresponding type constructor
      -- NB: Used when checking for incomplete pattern matching, since
      --     the type constructor keeps track of all its data constructors.
  }

instance Eq (NAME p) => Eq (TcCon p) where
  (==) = (==) `on` tcConCon

instance Ord (NAME p) => Ord (TcCon p) where
  compare = compare `on` tcConCon


-- * Operators

data Op = BoolOp BoolOp
        | IntOp IntOp
        | CONSOp          -- ^ ::
    deriving(Eq,Ord)

-- | Operators for building boolean expressions
data BoolOp = NotB
            | OrB
            | AndB
            | ImpB  -- ^ @==>@
            | IffB  -- ^ @<=>@
            | EqB   -- ^ @==@
            | NeqB  -- ^ @/=@
            | LtB
            | LeB
            | GtB
            | GeB
    deriving(Eq,Ord)

-- | Operators for building integer expressions
data IntOp = NegI   -- ^ negation @-@ /exp/
           | AddI
           | SubI
           | MulI
           | DivI   -- ^ @/@
           | ModI   -- ^ @%@
           | ExpI   -- ^ @^@
    deriving(Eq,Ord)


-- * Patterns

-- | A pattern, to be matched against a value.
-- NB: Only uniform patterns are supported. We believe this is convenient
--     for critical software development and it also makes pattern-matching
--     compilation a lot easier.
data Pat p where
  -- | variable
  VarPat :: !(VAR p) -> Pat p
  -- | literal constant
  LitPat :: !Lit -> Pat p
  -- | Infix @::@ (cons) pattern
  InfixCONSPat :: PostTcType p -> Pat p -> Pat p -> Pat p
  -- | data constructor and argument
  ConPat :: !(CON p) -> PostTcTypes p -> [Pat p] -> Pat p
  -- | tuple pattern
  TuplePat :: [Pat p] -> PostTcType p -> Pat p
  -- | list pattern
  ListPat :: [Pat p] -> PostTcType p -> Pat p
  -- | parenthesized pattern
  -- This makes pretty-printing easier.
  ParenPat :: Pat p -> Pat p
  -- | wildcard pattern (@_@)
  -- For convenience, those are converted into variables after renaming.
  WildPatIn :: Pat Pr
  WildPat :: Ge p Rn => !(VAR p) -> Pat p
  -- ^ as-pattern (@\@@)
  AsPat :: !(VAR p) -> Pat p -> Pat p

{- Note [Pattern signatures aka SigPat]
SigPats are banned to simplify things. For instance, we would expect
that an @-pattern can be eliminated by introducing a let-expression in
the RHS as in

  \l@(x::xs) -> x::l
  ===
  \(x::xs) -> let l = x::xs in x::l

but if we allow SigPats then the type of a variable may depend on a
variable introduced by a previous @-pattern making this conversion
impossible as in

  \p@(x::xs) (q:{q1:[Int] | head q1 == head p}) -> p ++ q

where you cannot simply move 'p' since the type of 'q' depends on it.

Also note that the main problem is caused by instantiation of
pattern-types... for normal expressions we could translate @-patterns
as specificed in the Haskell Report. 

Future work:
  a) Careful handling of @-patterns, potentially complicating
     functions for stuff like dependent-arrow instantiation.
  b) Syntactically restrict type annotations in patterns.
-}


-- * Types

data Type c p where
  -- | type variable
  VarTy :: !(TyVAR p) -> Type c p
  -- | named type or type constructor
  ConTyIn :: Lt p Tc => !(TyCON p) -> Type c p
  -- | application of a type constructor
  AppTyIn :: Lt p Tc => Tau p -> Tau p -> Type c p
  -- | saturated application of a type constructor
  -- NB: This type system is based on System F, not in System Fw.
  -- INV: The type constructor is not '[]', a case which is handled
  --      by 'ListTy'.
  ConTy :: Ge p Tc => !(TyCON p) -> [Tau p] -> Type c p
  -- | subset type
  PredTy :: Pat p -> Tau p -> Maybe (Prop p) -> Type c p
  -- | function type
  FunTy :: Dom p -> Range p -> Type c p
  -- | list type
  ListTy :: Tau p -> Type c p
  -- | tuple type
  TupleTy :: [Dom p] -> Type c p
  -- | parenthised type
  ParenTy :: Tau Pr -> Type c Pr 
  -- | meta type variable
  MetaTy :: !MetaTyVar -> Type c Tc
  -- | rank-1 polymorphic type
  ForallTy :: TyParams p -> Tau p -> Sigma p

type Sigma = Type SIGMA
type Tau   = Type TAU

  -- Even more conservative than purely syntactic equality.
  -- NB: If there are no subset types then it turns to be syntactic equality.
instance (Eq (TyVAR p), Eq (TyCON p)) => Eq (Type c p) where
  VarTy a == VarTy b = a == b
  ConTyIn tc1 == ConTyIn tc2 = tc1 == tc2
  AppTyIn tc1 ty1 == AppTyIn tc2 ty2
    = tc1 == tc2 && ty1 == ty2
  ConTy tc1 args1 == ConTy tc2 args2
    | length args1 == length args2 = tc1 == tc2 && and (zipWith (==) args1 args2)
  FunTy d1 r1 == FunTy d2 r2 = d1 == d2 && r1 == r2
  ListTy ty1 == ListTy ty2 = ty1 == ty2
  TupleTy ds1 == TupleTy ds2
    | length ds1 == length ds2 = and (zipWith (==) ds1 ds2)
  ParenTy ty1 == ParenTy ty2 = ty1 == ty2
  MetaTy mtv1 == MetaTy mtv2 = mtv1 == mtv2
  _ty1 == _ty2 = False


  -- NB: The @Dom Nothing ty (Just prop)@ is pointless
data Dom p = Dom {
               domMbPat  :: Maybe (Pat p)
             , domType   :: Tau p
             , domMbProp :: Maybe (Prop p)
             }

instance (Eq (TyVAR p), Eq (TyCON p)) => Eq (Dom p) where
  Dom Nothing ty1 Nothing == Dom Nothing ty2 Nothing = ty1 == ty2
  _dom1 == _dom2 = False


type Range = Tau

type PostTcType p = PostTc p (Tau p)
type PostTcTypes p = PostTc p [Tau p]

-- ** Meta type variables

data MetaTyVar = MetaTyV {
                    -- a 'Uniq' would suffice but a 'Name' allows
                    -- better pretty-printing.
                   mtvName :: !Name
                 , mtvKind :: !Kind
                 , mtvRef  :: IORef (Maybe (Tau Tc))
                 }

instance Eq MetaTyVar where
  (==) = (==) `on` mtvName

instance Ord MetaTyVar where
  compare = compare `on` mtvName

instance Named MetaTyVar where
  nameOf = mtvName


-- * Type constructors

type family TyCON phase
type instance TyCON Pr = TyName Pr
type instance TyCON Rn = TyName Rn
type instance TyCON Tc = TyCon Tc
type instance TyCON Ti = TyCon Ti


data TyName p = UserTyCon (UTyNAME p)
              | BuiltinTyCon BuiltinTyCon

deriving instance Eq (UTyNAME p) => Eq (TyName p)
deriving instance Ord (UTyNAME p) => Ord (TyName p)

  -- TODO: Should I include ListTyCon ?
  -- right now list is a built-in type (not a built-in type constructor)
  -- but just because list type has special syntax and in this way
  -- pretty-printing is slightly easier.
data BuiltinTyCon = UnitTyCon
                  | BoolTyCon
                  | IntTyCon
                  | NatTyCon    -- ^ @{n:Int|n >= 0}@
                  | ListTyCon
    deriving (Eq,Ord)


data TyCon p
  = AlgTyCon {
      tyConName   :: TyName p
    , tyConCons   :: [Con p]
    }
  | SynTyCon {
      tyConName   :: TyName p
    , tyConParams :: [TyVar]
    , synTyConRhs :: Tau p
    }

instance Eq (TyName p) => Eq (TyCon p) where
  (==) = (==) `on` tyConName

instance Ord (TyName p) => Ord (TyCon p) where
  compare = compare `on` tyConName


-- * Kinds

data Kind = TypeKi
          | FunKi Kind Kind
    deriving Eq

type PostTcKind p = PostTc p Kind
