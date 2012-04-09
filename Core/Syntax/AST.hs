{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Core.Syntax.AST where

import Name
import Sorted
import Unique( Uniquable(..), MonadUnique(..) )

import Data.Data ( Data, Typeable )
import Data.Function ( on )
import qualified Data.Generics.Uniplate.Data as G
import Data.IntMap ( IntMap )
import Data.Sequence ( Seq )

import Unsafe.Coerce ( unsafeCoerce )


-- * Variables

  -- | A typed 'Name'
data Var
  = V {
      varName   :: !Name
    , varType   :: Sigma
    , skolemVar :: !Bool
    }
    deriving(Typeable,Data)

varTau :: Var -> Tau
varTau = sigma2tau . varType

mkVar :: Name -> Sigma -> Var
mkVar name ty = V name ty False

mkSkVar :: Name -> Sigma -> Var
mkSkVar name ty = V name ty True

instance Eq Var where
  (==) = (==) `on` varName

instance Ord Var where
  compare = compare `on` varName

instance Named Var where
  nameOf = varName

instance Uniquable Var where
  uniqOf = uniqOf . nameOf

instance Sorted Var Sigma where
  sortOf = varType


  -- | Essentially a kinded 'Name'
data TyVar
  = TyV {
      tyVarName   :: !Name
    , tyVarKind   :: !Kind
    , skolemTyVar :: !Bool
         -- ^ Is it a skolem type variable ?
    }
    deriving(Typeable,Data)

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

-- ** Fresh variables

newVar :: MonadUnique m => String -> Sigma -> m Var
newVar str ty = do name <- newName VarNS str
                   return $ mkVar name ty

newVarFrom :: MonadUnique m => Var -> m Var
newVarFrom (V name ty isSk) = do
  name' <- newNameFrom name
  return $ V name' ty isSk

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

-- ** Parameters

type Params = [Pat]

type TyParams = [TyVar]

-- * Modules

data Module = Module {
      modName :: ModuleName
    , modDecls :: [Decl]
    , modTCCs :: IntMap TCC
    }
    deriving(Eq,Typeable,Data)

newtype ModuleName = ModName String
    deriving(Eq,Typeable,Data)

-- * Declarations

data Decl = TypeDecl TyVar TyParams Tau
              -- ^ type synonym
          | DataDecl TyVar TyParams [ConDecl]
              -- ^ inductive data type
          | ValDecl Bind
              -- ^ Value declarations
          | GoalDecl GoalType Name TyParams Prop
              -- ^ logical goal (theorem or lemma)
    deriving(Eq,Typeable,Data)

data Bind = FunBind IsRec Var [TyVar] [Var] Rhs -- [Match]
                -- ^ a function defined by a *set* of equations
                -- NB: Only uniform definitions are allowed
--           | PatBind Pat Rhs
--                 -- ^ pattern binding
    deriving(Eq,Typeable,Data)

-- type WhereBinds = [Bind]

data IsRec = Rec
           | NonRec
    deriving (Eq,Typeable,Data)

-- | Declaration of a data constructor.
data ConDecl = ConDecl Var [Dom]
    deriving (Eq,Typeable,Data)

data GoalType = TheoremGoal
              | LemmaGoal
    deriving(Eq,Typeable,Data)

mkSimpleBind :: Var -> Rhs -> Bind
mkSimpleBind x rhs = FunBind NonRec x [] [] rhs

-- * Expressions

data Exp = Var Var -- ^ variable
         | Con Con -- ^ data constructor
         | Lit Lit -- ^ literal constant
--          | Undefined
         | PrefixApp OpExp Exp --  ^ prefix application
         | InfixApp Exp OpExp Exp -- ^ infix application
         | App Exp Exp
            -- ^ application
         | TyApp Exp [Tau]
            -- ^ type application
         | Lam [Var] LamRHS
            -- ^ lambda expression
         | Let [Bind] Exp -- ^ local declarations with @let@
         | TyLam [TyVar] Exp  -- ^ type lambda
         | Ite Tau Prop Exp Exp -- ^ @if@ /exp/ @then@ /exp/ @else@ /exp/
         | If Tau GuardedRhss -- ^ Generalized @if@ expressions
         -- | @case@ /exp/ @of@ /alts/
         | Case Tau -- ^ the type of the whole case expression
                Exp
                [Alt]
         | Tuple Tau [Exp] -- ^ tuple expression
         | List Tau [Exp] -- ^ list expression
         | Paren Exp -- ^ parenthesized expression
         | EnumFromTo Exp Exp -- ^ bounded arithmetic sequence, incrementing by 1
         | EnumFromThenTo Exp Exp Exp -- ^ bounded arithmetic sequence, with first two elements given
         | Coerc Exp Sigma -- ^ explicit type coercion
         | QP Quantifier [Var] Prop -- ^ logic quantifier
    deriving(Eq,Typeable,Data)


-- | An Op or a TyApp on an Op
data OpExp = OpExp [Tau] Op
    deriving(Eq,Typeable,Data)

-- | Expressions of boolean type
type Prop = Exp

mkIntLit :: Integer -> Exp
mkIntLit = Lit . IntLit

mkTrue :: Prop
mkTrue = Con trueCon

mkFalse :: Prop
mkFalse = Con falseCon

mkNot :: Prop -> Prop
mkNot p = PrefixApp (OpExp [] (BoolOp NotB)) p

mkNeg :: Exp -> Exp
mkNeg e = PrefixApp (OpExp [] (IntOp NegI)) e

splitApp :: Exp -> (Exp,[Exp])
splitApp = go []
  where go args (App f a) = go (a:args) f
        go args f         = (f,args)

mkLet :: [Bind] -> Exp -> Exp
mkLet [] e = e
mkLet bs e = Let bs e

mkTyApp :: Exp -> [Tau] -> Exp
mkTyApp expr []  = expr
mkTyApp expr tys = TyApp expr tys

mkTyLam :: [TyVar] -> Exp -> Exp
mkTyLam [] expr  = expr
mkTyLam tvs expr = TyLam tvs expr

-- ** Right-hand side

-- | The right hand side of a function or pattern binding.
-- NB: A Rhs has always a Tau type.
data Rhs = Rhs Tau Exp
    deriving(Eq,Typeable,Data)

data GuardedRhss = GuardedRhss [GuardedRhs]
                               (Maybe Exp) -- ^ else
    deriving(Eq,Typeable,Data)

data GuardedRhs = GuardedRhs Prop Exp
    deriving(Eq,Typeable,Data)

-- | RHS of a lamba-abstraction
-- Invariant: no guards nor `where' bindings
type LamRHS = Rhs

rhsExp :: Tau -> Exp -> Rhs
rhsExp = Rhs

-- ** Patterns

-- | A pattern, to be matched against a value.
data Pat = VarPat Var
            -- ^ variable
         | LitPat Lit
            -- ^ literal constant
         | ConPat [Tau] Con [Pat]
            -- ^ data constructor pattern
         | TuplePat Tau [Pat]
            -- ^ tuple pattern
--          | ListPat Tau [Pat]
--             -- ^ list pattern
         | ParenPat Pat
            -- ^ parenthesized pattern
  deriving(Eq,Typeable,Data)

-- | A very basic, non-nested pattern
-- No ParenPat's allowed
type SPat = Pat

-- isVarPat :: Pat p -> Bool
-- isVarPat (VarPat _) = True
-- isVarPat _other     = False

mkNILPat :: Tau -> Pat
mkNILPat ty = ConPat [ty] nilCon []

mkCONSPat :: Tau -> Pat -> Pat -> Pat
mkCONSPat ty p1 p2 = ConPat [ty] consCon [p1,p2]

pat2exp :: Pat -> Exp
pat2exp (LitPat lit) = Lit lit
pat2exp (VarPat x)   = Var x
pat2exp (ConPat [elem_ty] (BuiltinCon ConsCon) [p1,p2])
  = InfixApp (pat2exp p1) consE (pat2exp p2)
  where consE = OpExp [elem_ty] CONSOp
pat2exp (ConPat typs con ps)
  = conE `mkApp` map pat2exp ps
  where conE = mkTyApp (Con con) typs
pat2exp (TuplePat tup_ty ps) = Tuple tup_ty $ map pat2exp ps
pat2exp (ParenPat p) = Paren $ pat2exp p

rmParenPat :: Pat -> Pat
rmParenPat = G.transform f
  where f (ParenPat p) = p
        f pat          = pat

-- | An /alt/ in a @case@ expression.
data Alt = Alt SPat Rhs
    deriving(Eq,Typeable,Data)

-- ** Literals

data Lit = IntLit Integer
    deriving(Eq,Typeable,Data)

-- ** Data constructors

data Con = UserCon Var
         | BuiltinCon BuiltinCon
  deriving(Eq,Ord,Typeable,Data)

data BuiltinCon = UnitCon
                | FalseCon
                | TrueCon
                | NilCon
                | ConsCon
    deriving(Eq,Ord,Typeable,Data)

instance Sorted BuiltinCon Sigma where
  sortOf UnitCon  = unitTy
  sortOf FalseCon = boolTy
  sortOf TrueCon  = boolTy
  sortOf NilCon   = mkForallTy [a_tv] $ ListTy a
    where a_nm = mkUsrName (mkOccName TyVarNS "a") a_uniq
          a_uniq = -1001
          a_tv = TyV a_nm typeKi False
          a = VarTy a_tv
  sortOf ConsCon  = mkForallTy [a_tv] $ a --> ListTy a --> ListTy a
    where a_nm = mkUsrName (mkOccName TyVarNS "a") a_uniq
          a_uniq = -1002
          a_tv = TyV a_nm typeKi False
          a = VarTy a_tv

instance Sorted Con Sigma where
  sortOf (UserCon ucon)    = sortOf ucon
  sortOf (BuiltinCon bcon) = sortOf bcon

-- data TcCon p = TcCon {
--     tcConCon :: Con p
--   , tcConTy  :: TyCon p
--   }

-- instance Eq (NAME p) => Eq (TcCon p) where
--   (==) = (==) `on` tcConCon

-- instance Ord (NAME p) => Ord (TcCon p) where
--   compare = compare `on` tcConCon

-- instance IsPostTc p => Sorted (TcCon p) (Sigma p) where
--   sortOf = sortOf . tcConCon

unitCon, trueCon, falseCon, nilCon, consCon :: Con
unitCon  = BuiltinCon UnitCon
trueCon  = BuiltinCon TrueCon
falseCon = BuiltinCon FalseCon
nilCon   = BuiltinCon NilCon
consCon  = BuiltinCon ConsCon

-- tcUnitCon, tcTrueCon, tcFalseCon, tcNilCon, tcConsCon :: IsPostTc p => TcCon p
-- tcUnitCon  = TcCon unitCon unitTyCon
-- tcTrueCon  = TcCon trueCon boolTyCon
-- tcFalseCon = TcCon falseCon boolTyCon
-- tcNilCon   = TcCon nilCon listTyCon
-- tcConsCon  = TcCon consCon listTyCon

-- ** Built-in operators

data Op = BoolOp BoolOp
        | IntOp IntOp
        | CONSOp
    deriving(Eq,Ord,Typeable,Data)

instance Sorted Op Sigma where
  sortOf (BoolOp bop) = sortOf bop
  sortOf (IntOp iop)  = sortOf iop
  sortOf CONSOp       = sortOf ConsCon

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
    deriving(Eq,Ord,Typeable,Data)

instance Sorted BoolOp Sigma where
  sortOf NotB = boolTy --> boolTy
  sortOf OrB = boolTy --> boolTy --> boolTy
  sortOf AndB = boolTy --> boolTy --> boolTy
  sortOf ImpB = boolTy --> boolTy --> boolTy
  sortOf IffB = boolTy --> boolTy --> boolTy
  sortOf EqB  = mkForallTy [a_tv] $ a --> a --> boolTy
    where a_nm = mkUsrName (mkOccName TyVarNS "a") a_uniq
          a_uniq = -2001
          a_tv = TyV a_nm typeKi False
          a = VarTy a_tv
  sortOf NeqB  = mkForallTy [a_tv] $ a --> a --> boolTy
    where a_nm = mkUsrName (mkOccName TyVarNS "a") a_uniq
          a_uniq = -2002
          a_tv = TyV a_nm typeKi False
          a = VarTy a_tv
  sortOf LtB = intTy --> intTy --> boolTy
  sortOf LeB = intTy --> intTy --> boolTy
  sortOf GtB = intTy --> intTy --> boolTy
  sortOf GeB = intTy --> intTy --> boolTy

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
    deriving(Eq,Ord,Typeable,Data)

  -- / and % could be more specific but that would introduce a mutually recursive
  -- dependency between both of them: that should be OK since they are built-in, but
  -- since the language does not allow you to do that.. we don't allow that as well.
  -- we may provide some assumed theorems, for instance
  -- theorem div_mod = forall n m, (n/m) * m + (n%m) == n
instance Sorted IntOp Sigma where
  sortOf NegI = intTy --> intTy
  sortOf AddI = intTy --> intTy --> intTy
  sortOf SubI = intTy --> intTy --> intTy
  sortOf MulI = intTy --> intTy --> intTy
  sortOf DivI = intTy
                  --> mkDomVar m intTy (Var m ./=. lit_0)
                  |-> intTy
    where m = mkVar m_nm intTy
          m_nm = mkSysName (mkOccName VarNS "m") m_uniq
          m_uniq = -3002
  sortOf ModI = intTy
                  --> mkDomVar m intTy (Var m ./=. lit_0)
                  |-> intTy
    where m = mkVar m_nm intTy
          m_nm = mkSysName (mkOccName VarNS "m") m_uniq
          m_uniq = -3102
  sortOf ExpI = intTy --> intTy --> intTy

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
    deriving(Eq,Typeable,Data)

-- ** Constructors

lit_0 :: Exp
lit_0 = Lit (IntLit 0)

mkInt :: Integer -> Exp
mkInt = Lit . IntLit

mkApp :: Exp -> [Exp] -> Exp
mkApp f args = foldl App f args

mkInfixApp :: Op -> [Tau] -> Exp -> Exp -> Exp
mkInfixApp op tys e1 e2 = InfixApp e1 (OpExp tys op) e2

mkMonoInfixApp :: Op -> Exp -> Exp -> Exp
mkMonoInfixApp op = mkInfixApp op []

(.<.), (.<=.), (.>.), (.>=.) :: Exp -> Exp -> Prop
x .<. y = mkInfixApp ltOp [] x y
x .<=. y = mkInfixApp leOp [] x y
x .>. y = mkInfixApp gtOp [] x y
x .>=. y = mkInfixApp geOp [] x y

(.==.), (./=.) :: Exp -> Exp -> Prop
x .==. y = mkInfixApp eqOp [intTy] x y
x ./=. y = mkInfixApp neqOp [intTy] x y

(.+.), (.-.), (.*.), (./.) :: Exp -> Exp -> Exp
x .+. y = mkInfixApp addOp [] x y
x .-. y = mkInfixApp subOp [] x y
x .*. y = mkInfixApp mulOp [] x y
x ./. y = mkInfixApp divOp [] x y

-- * Types

-- typeOf :: Sorted a (Type c p) => a -> Type c p
-- typeOf = sortOf

mkForallTy :: [TyVar] -> Tau -> Sigma
mkForallTy []  tau = tau2sigma tau
mkForallTy tvs tau = ForallTy tvs tau

splitSigma :: Sigma -> (TyParams,Tau)
splitSigma (ForallTy tvs tau) = (tvs,tau)
splitSigma ty                 = ([],sigma2tau ty)

qTyVars :: Sigma -> [TyVar]
qTyVars (ForallTy tvs _) = tvs
qTyVars _other           = []

tau2sigma :: Tau -> Sigma
tau2sigma = unsafeCoerce

tau2type :: Tau -> Type c
tau2type = unsafeCoerce

sigma2tau :: Sigma -> Tau
sigma2tau (ForallTy _ _) = error "bug sigma2tau"  -- FIX
sigma2tau ty             = unsafeCoerce ty

data Type c
  = VarTy TyVar
      -- ^ type variable
  | ConTy TyCon [Tau]
      -- ^ application of a type constructor
  | PredTy Pat Tau (Maybe Prop)
      -- ^ subset type
  | FunTy Dom Range
      -- ^ function type
  | ListTy Tau
      -- ^ list type
  | TupleTy [Dom]
      -- ^ tuple type
  | ForallTy [TyVar] Tau
      -- ^ polymorphic type
    deriving(Eq,Typeable,Data)

type Sigma = Type SIGMA
type Tau   = Type TAU

  -- NB: The @Dom Nothing ty (Just prop)@ is pointless
data Dom
  = Dom {
      domMbPat  :: Maybe Pat
    , domType   :: Tau
    , domMbProp :: Maybe Prop
    }
    deriving(Eq,Typeable,Data)

dom2type :: Dom -> Tau
dom2type (Dom Nothing ty Nothing)    = ty
dom2type (Dom (Just pat) ty mb_prop) = mkPredTy pat ty mb_prop
dom2type _other                      = undefined -- impossible

type Range = Tau

isVarTy :: Type c -> Bool
isVarTy (VarTy _) = True
isVarTy _ty       = False

isFunTy :: Tau -> Bool
isFunTy ty
  | FunTy _ _ <- mu_0 ty = True
  | otherwise            = False

  -- (args,result)
splitFunTy :: Tau -> ([Dom],Tau)
splitFunTy ty
 | FunTy a t <- mu_0 ty
 , let (args,res) = splitFunTy t
 = (a:args,res)
splitFunTy ty = ([],ty)

-- splitFunTyN :: Int -> Tau p -> ([Dom p],Tau p)
-- splitFunTyN 0 ty = ([],ty)
-- splitFunTyN n ty
--  | FunTy a t <- mu_0 ty
--  , let (args,res) = splitFunTyN (n-1) t
--  = (a:args,res)
-- splitFunTyN _ ty = ([],ty)

-- funTyArity :: Tau p -> Int
-- funTyArity ty = length args
--   where (args,_res) = splitFunTy ty

-- | Removes outermost predicate-types
mu_0 :: Tau -> Tau
mu_0 (PredTy _ ty _) = mu_0 ty
mu_0 ty              = ty

isSynTy :: Type c -> Bool
isSynTy (ConTy SynTyCon{} _) = True
isSynTy _other               = False

-- ** Type constructors

data TyName = UserTyCon TyVar
            | BuiltinTyCon BuiltinTyCon
    deriving(Eq,Ord,Typeable,Data)

data BuiltinTyCon = UnitTyCon
                  | BoolTyCon
                  | IntTyCon
                  | NatTyCon    -- ^ @{n:Int|n >= 0}@
                  | ListTyCon
    deriving(Eq,Ord,Typeable,Data)

instance Sorted TyName Kind where
  sortOf (UserTyCon utycon)    = sortOf utycon
  sortOf (BuiltinTyCon btycon) = sortOf btycon

data TyCon
  = AlgTyCon {
      tyConName   :: TyName
--     , tyConCons   :: [Con p]
--     , tyConParams :: [TyVar]
    }
  | SynTyCon {
      tyConName   :: TyName
    , tyConParams :: [TyVar]
    , synTyConRhs :: Tau
    }
    deriving(Eq,Typeable,Data)

instance Ord TyCon where
  compare = compare `on` tyConName

instance Sorted TyCon Kind where
  sortOf = sortOf . tyConName

unitTyName, boolTyName, intTyName, natTyName :: TyName
unitTyName = BuiltinTyCon UnitTyCon
boolTyName = BuiltinTyCon BoolTyCon
intTyName  = BuiltinTyCon IntTyCon
natTyName  = BuiltinTyCon NatTyCon

unitTyCon, boolTyCon, intTyCon, natTyCon, listTyCon :: TyCon
unitTyCon = AlgTyCon {
              tyConName = unitTyName
--             , tyConParams = []
--             , tyConCons = [unitCon]
            }
boolTyCon = AlgTyCon {
              tyConName   = boolTyName
--             , tyConParams = []
--             , tyConCons = [falseCon,trueCon]
            }
intTyCon  = AlgTyCon {
              tyConName   = intTyName
--             , tyConParams = []
--             , tyConCons = []  -- special case, infinite constructors!
            }
natTyCon  = SynTyCon {
              tyConName   = natTyName
            , tyConParams = []
            , synTyConRhs = mkPredTy (VarPat n) intTy (Just $ (Var n) .>=. (Lit (IntLit 0)))
            }
  where n = mkVar n_nm intTy
        n_nm = mkSysName (mkOccName VarNS "n") n_uniq
        n_uniq = -4001
listTyCon = AlgTyCon {
              tyConName   = BuiltinTyCon ListTyCon
--             , tyConParams = []
--             , tyConCons = [nilCon,consCon]
            }

instance Sorted BuiltinTyCon Kind where
  sortOf UnitTyCon = typeKi
  sortOf BoolTyCon = typeKi
  sortOf IntTyCon  = typeKi
  sortOf NatTyCon  = typeKi
  sortOf ListTyCon = typeKi ++> typeKi

-- ** Constructors

infixr |->, -->


(|->) :: Dom -> Range -> Tau
(|->) = FunTy

(-->) :: Tau -> Tau -> Type c
dom --> rang = tau2type $ Dom Nothing dom Nothing |-> rang

mkFunTy :: [Dom] -> Range -> Type c
mkFunTy doms rang = tau2type $ foldr (|->) rang doms

type2dom :: Tau -> Dom
type2dom ty = Dom Nothing ty Nothing

mkDom :: Pat -> Tau -> Prop -> Dom
mkDom pat ty prop = Dom (Just pat) ty (Just prop)


mkDomVar :: Var -> Tau -> Prop -> Dom
mkDomVar x ty prop = mkDom (VarPat x) ty prop

mkPatternDom :: Pat -> Tau -> Dom
mkPatternDom pat ty = Dom (Just pat) ty Nothing

mkVarDom :: Var -> Tau -> Dom
mkVarDom x = mkPatternDom (VarPat x)

mkPatternTy :: Pat -> Tau -> Tau
mkPatternTy (VarPat _)  ty = ty
mkPatternTy pat         ty = PredTy pat ty Nothing

mkPredTy :: Pat -> Tau -> Maybe Prop -> Tau
mkPredTy pat ty Nothing = mkPatternTy pat ty
mkPredTy pat ty prop    = PredTy pat ty prop

unitTy, boolTy, intTy, natTy :: Type c
unitTy = ConTy unitTyCon []
boolTy = ConTy boolTyCon []
intTy  = ConTy intTyCon []
natTy  = ConTy natTyCon []


-- * Kinds

kindOf :: Sorted a Kind => a -> Kind
kindOf = sortOf

data Kind = TypeKi
          | FunKi Kind Kind
    deriving(Eq,Typeable,Data)

-- ** Constructors

infixr ++>

typeKi :: Kind
typeKi = TypeKi

(++>) :: Kind -> Kind -> Kind
(++>) = FunKi

mkFunKi :: [Kind] -> Kind -> Kind
mkFunKi doms rang =  foldr (++>) rang doms


-- * TCCs

data TccHypoThing = ForAll [Var]
                  | LetIn [Bind]
                  | Facts [Prop]
    deriving(Eq,Typeable,Data)

type TccPropCtxt = Seq TccHypoThing

data TCC
  = CoercionTCC {
      tccSrcCtxt  :: !String
    , tccPropCtxt :: TccPropCtxt
    , tccExpr     :: Exp
    , tccActType  :: Sigma
    , tccExpType  :: Sigma
    }
  | CompletenessTCC {
      tccSrcCtxt  :: !String
    , tccPropCtxt :: TccPropCtxt
    , tccProps    :: Prop
    }
    deriving(Eq,Typeable,Data)
