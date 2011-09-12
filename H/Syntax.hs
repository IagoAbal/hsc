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

import Unsafe.Coerce ( unsafeCoerce )


-- * Variables

  -- | A typed 'Name'
data Var p = V {
               varName   :: !Name
             , varType   :: Sigma p
             , skolemVar :: !Bool
             }

mkVar :: Name -> Sigma p -> Var p
mkVar name sig = V name sig False

mkSkVar :: Name -> Sigma p -> Var p
mkSkVar name sig = V name sig True

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

instance Pretty (Var p) where
  pretty = pretty . varName

instance PrettyNames p => PrettyBndr (Var p) where
  prettyBndr x = parens $ pretty x <> colon <> pretty (varType x)

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

instance PrettyBndr TyVar where
  prettyBndr tv = parens $ pretty tv <> colon <> pretty (tyVarKind tv)

-- ** Fresh variables

newVar :: MonadUnique m => String -> Sigma p -> m (Var p)
newVar str ty = do name <- newName VarNS str
                   return $ V name ty False

newVarFrom :: MonadUnique m => Var p -> m (Var p)
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
type instance TyCON Ti = TyCon Ti

type family GoalNAME phase
type instance GoalNAME Pr = OccName
type instance GoalNAME Rn = Name
type instance GoalNAME Tc = Name
type instance GoalNAME Ti = Name
type instance GoalNAME Vc = Name


class (Pretty (VAR p), PrettyBndr (VAR p), Pretty (TyVAR p), PrettyBndr (TyVAR p), Pretty (TyCON p), Pretty(GoalNAME p)) => PrettyNames p where
instance PrettyNames Pr where
instance PrettyNames Rn where
instance PrettyNames Tc where
instance PrettyNames Ti where

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

-- * IsPostTc

class (Ge p Tc, VAR p ~ Var p, TyVAR p ~ TyVar, TyCON p ~ TyCon p, GoalNAME p ~ Name, PrettyNames p) => IsPostTc p where

instance IsPostTc Tc where
instance IsPostTc Ti where

-- * Modules

data Module p = Module SrcLoc ModuleName [Decl p]


newtype ModuleName = ModName String


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

data Decl p where
  -- | type synonym 
  TypeDecl ::	SrcLoc -> UTyNAME p -> TyParams p -> Tau p -> Decl p
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


data Bind p = FunBind (IsRec p) (NAME p) (TypeSig p) (PostTcTyParams p) [Match p]
                  -- ^ a function defined by a *set* of equations
                  -- NB: Only uniform definitions are allowed
                  -- NB: @f = ...@ is considered a FunBind because that allows
                  --     the annotation with a polymorphic type.
            | PatBind (Maybe SrcLoc) (Pat p) (Rhs p)
                  -- ^ pattern binding

data TypeSig p = NoTypeSig
               | TypeSig SrcLoc (Sigma p)

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
  ConDeclIn :: SrcLoc -> NAME Pr -> [Tau Pr] -> ConDecl Pr
  ConDecl :: Ge p Rn => SrcLoc -> NAME p -> [Dom p] -> ConDecl p

-- | Clauses of a function binding.
data Match p
	 = Match (Maybe SrcLoc) [Pat p] (Rhs p)

data GoalType = TheoremGoal
              | LemmaGoal
  deriving Eq


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
  pretty (GoalDecl _pos goaltype gname _ptctys prop)
    = blankline $
        myFsep [pretty goaltype, pretty gname, equals, pretty prop]

instance Pretty GoalType where
  pretty TheoremGoal = text "theorem"
  pretty LemmaGoal   = text "lemma"

instance PrettyNames p => Pretty (Bind p) where
  pretty (FunBind _rec fun sig _ matches) =
         ppTypeSig fun sig
      $$ ppBindings (map (ppMatch fun) matches)
  pretty (PatBind _pos pat (Rhs grhs whereDecls)) =
    myFsep [pretty pat, ppGRhs ValDef grhs]
        $$$ ppWhere whereDecls

ppTypeSig :: PrettyNames p => NAME p -> TypeSig p -> Doc
ppTypeSig _fun NoTypeSig = empty
ppTypeSig  fun (TypeSig _loc polyty) = mySep [pretty fun, text ":", pretty polyty]

ppMatch :: PrettyNames p => NAME p -> Match p -> Doc
ppMatch fun (Match _pos ps (Rhs grhs whereDecls)) =
    myFsep (lhs ++ [ppGRhs ValDef grhs])
    $$$ ppWhere whereDecls
      where
    lhs = prettyBndr fun : map (prettyPrec 2) ps

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
  -- | operator
  Op  :: Op -> Exp p
  -- | literal constant
  Lit :: Lit -> Exp p
  -- | @else@ guard expression
  -- It is used to facilitate parsing but then removed during renaming
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
  Lam :: Maybe SrcLoc -> [Pat p] -> Exp p -> Exp p
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
  Tuple :: PostTcType p -> [Exp p] -> Exp p
  -- | list expression
  List :: PostTcType p -> [Exp p] -> Exp p
  -- | parenthesized expression
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
  Coerc :: SrcLoc -> Exp p -> Sigma p -> Exp p
  -- | logic quantifier
  QP :: Quantifier -> [Pat p] -> Prop p -> Prop p

-- | An Op or a TyApp on an Op
type OpExp = Exp

-- | Expressions of boolean type
type Prop = Exp

isElseGuard :: Exp Pr -> Bool
isElseGuard ElseGuard = True
isElseGuard _other    = False

splitApp :: Exp p -> (Exp p,[Exp p])
splitApp = go []
  where go args (App f a) = go (a:args) f
        go args f         = (f,args)

tyApp :: (Ge p Tc) => Exp p -> [Tau p] -> Exp p
tyApp expr []  = expr
tyApp expr tys = TyApp expr tys

tyLam :: (Ge p Tc, TyVAR p ~ TyVar) => [TyVar] -> Exp p -> Exp p
tyLam [] expr  = expr
tyLam tvs expr = TyLam tvs expr

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
  pretty (Lam _loc patList body) = myFsep $
    char '\\' : map pretty patList ++ [text "->", pretty body]
  pretty (TyApp e tys) = myFsep $ pretty e : map (\ty -> char '@' <> ppAType ty) tys
  pretty (TyLam tvs body) = myFsep $ char '\\' : map prettyBndr tvs ++ [text "->", pretty body]
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
  pretty (Con con) = ppPrefixCon con
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

rhsExp :: Exp p -> Rhs p
rhsExp e = Rhs (UnGuarded e) []

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
ppElse  ctx (Else _pos body)
  = myFsep [char '|', text "else", rhsSepSym ctx, pretty body]
ppElse _ctx  NoElse   = empty

-- ** Patterns

-- | A pattern, to be matched against a value.
data Pat p where
  -- | variable
  VarPat :: VAR p -> Pat p
  -- | literal constant
  LitPat :: Lit -> Pat p
  -- | pattern with infix data constructor
  InfixPat :: Pat p -> BuiltinCon -> PostTcTypes p -> Pat p -> Pat p
  -- | data constructor and argument
  ConPat :: Con p -> PostTcTypes p -> [Pat p] -> Pat p
  -- | tuple pattern
  TuplePat :: [Pat p] -> PostTcType p -> Pat p
  -- | list pattern
  ListPat :: [Pat p] -> PostTcType p -> Pat p
  -- | parenthesized pattern
  ParenPat :: Pat p -> Pat p
  -- | wildcard pattern (@_@)
  WildPat :: PostTcType p -> Pat p
  -- ^ as-pattern (@\@@)
  AsPat :: VAR p -> Pat p -> Pat p
  -- ^ pattern signature
    -- Add SrcLoc ?
  SigPat :: Pat p -> Tau p -> Pat p

-- | An /alt/ in a @case@ expression.
data Alt p = Alt (Maybe SrcLoc) (Pat p) (Rhs p)

patBndrs :: Pat p -> [VAR p]
patBndrs (VarPat var) = [var]
patBndrs (LitPat _lit) = []
patBndrs (InfixPat p1 _op _ p2) = patBndrs p1 ++ patBndrs p2
patBndrs (ConPat _con _ ps) = patsBndrs ps
patBndrs (TuplePat ps _) = patsBndrs ps
patBndrs (ListPat ps _) = patsBndrs ps
patBndrs (ParenPat p) = patBndrs p
patBndrs (WildPat _)  = []
patBndrs (AsPat v p)  = v : patBndrs p
patBndrs (SigPat p _t) = patBndrs p

patsBndrs :: [Pat p] -> [VAR p]
patsBndrs = concatMap patBndrs


-- | Check if an arbitrary expression could be matched against some
-- given pattern. This is an undecidable problem and since the purpose of
-- this function is to detect trivial errors, it is conservative
-- considering that an expression may match a pattern in case of doubt.
-- NB: It *requires* that the given expression and pattern have compatible types.
-- e.g. @Just 1 `matchableWith` Nothing == False@
-- e.g. @tail [x] `matchableWith (y::ys) == True@
matchableWith :: IsPostTc p => Exp p -> Pat p -> Bool
matchableWith _e            (VarPat _)    = True
matchableWith _e            (WildPat _)   = True
matchableWith (Lit lit)     (LitPat lit') = lit == lit'
  -- 'p' is not a 'VarPar' nor a 'LitPat' so matching is not possible
matchableWith (Lit _)       _p            = False
matchableWith (List _ es)   (ListPat ps _)
  | length es == length ps = and $ zipWith matchableWith es ps
  | otherwise              = False
  -- if types are compatible then @length es == length ps@
matchableWith (Tuple _ es)  (TuplePat ps _)
  = and $ zipWith matchableWith es ps
matchableWith e             p
  | Just (con,es) <- splitConApp e
  , ConPat con' _ ps <- p = if con == con'
                              then and $ zipWith matchableWith es ps
                              else False
    -- 'con' is a data constructor with no arguments, but 'InfixPat'
    -- implies a binary data constructor, here we detect that '[]'
    -- does not match _::_.
  | Just (_con,[]) <- splitConApp e
  , InfixPat _ _ _ _ <- p = False
  where get_con (Con con)     = Just con
        get_con (TyApp e1 _)   = get_con e1
        get_con (Paren e1)     = get_con e1
        get_con (Coerc _ e1 _) = get_con e1
        get_con _other        = Nothing
        splitConApp e1 | Just con <- get_con f = Just (con,args)
                       | otherwise             = Nothing
          where (f,args) = splitApp e1
-- 'InfixApp'/'InfixPat' case is beign ignored for now because it is not
-- very interesting since only '::' can be used in a 'InfixPat'.
matchableWith (List _ [])   (InfixPat _ _ _ _) = False
  -- since 'e' and 'p' are type-compatible and 'p' arguments are null,
  -- then we know 'p' is a '[]' pattern.
matchableWith (List _ (_:_)) (ConPat _ _ []) = False
matchableWith (List a (e:es)) (InfixPat p _ _ ps)
  = matchableWith e p && matchableWith (List a es) ps
matchableWith e             (SigPat p _) = matchableWith e p
matchableWith (Coerc _ e _) p            = matchableWith e p
matchableWith (Paren e)     p            = matchableWith e p
matchableWith e             (ParenPat p) = matchableWith e p
  -- otherwise, be conversative and consider that 'e' matches 'p'
matchableWith _e            _p           = True

-- | Checks if two patterns are 'matchable', in the sense that their
-- "shapes" can be matched one against the other.
-- Some examples:
--   @matchablePats (_::_) (x::xs) == True@
--   @matchablePats [1,2,x] [1,2,_] == Truee@
--   @matchablePats (_::_) [] == False@
--   @matchablePats (1,b) (x,y) == True@
--   @matchablePats (a,b,c) (x,y) == False@
-- Note that this check does not detect any possible inconsistency,
-- for instance @matchablePats (x1::x2::xs) (y::(ys:{[]:[Int]})) == True@.
matchablePats :: IsPostTc p => Pat p -> Pat p -> Bool
matchablePats (VarPat _)  _           = True
matchablePats (WildPat _)    _           = True
matchablePats _           (VarPat _)  = True
matchablePats _           (WildPat _)     = True
matchablePats (LitPat l1) (LitPat l2) = l1 == l2
matchablePats (InfixPat p1 bcon _ p2) (InfixPat p1' bcon' _ p2')
  = bcon == bcon' && matchablePats p1 p1' && matchablePats p2 p2'
matchablePats (ConPat con _ ps) (ConPat con' _ ps')
  = con == con' && and (zipWith matchablePats ps ps')
matchablePats (TuplePat ps _) (TuplePat ps' _)
  = length ps == length ps' && and (zipWith matchablePats ps ps')
matchablePats (ListPat ps _) (ListPat ps' _)
  = length ps == length ps' && and (zipWith matchablePats ps ps')
matchablePats (ListPat (p:ps) ptcty) (InfixPat p' _ _ q)
  = matchablePats p p' && matchablePats (ListPat ps ptcty) q
matchablePats (InfixPat p _ _ q) (ListPat (p':ps') ptcty)
  = matchablePats p p' && matchablePats (ListPat ps' ptcty) q
matchablePats (ListPat [] _) (ConPat _ _ []) = True
matchablePats (ConPat _ _ []) (ListPat [] _) = True
matchablePats (ParenPat p) p'            = matchablePats p p'
matchablePats p            (ParenPat p') = matchablePats p p'
matchablePats (AsPat _ p)  p'            = matchablePats p p'
matchablePats p            (AsPat _ p')  = matchablePats p p'
matchablePats (SigPat p _) p'            = matchablePats p p'
matchablePats p            (SigPat p' _) = matchablePats p p'
matchablePats _p           _p'           = False



instance PrettyNames p => Pretty (Pat p) where
    -- special case
  prettyPrec _ (SigPat (VarPat var) ty) =
    parens $ myFsep [pretty var, text ":", pretty ty]
    -- special case
  prettyPrec _ (SigPat (AsPat var pat) ty) =
    parens $ myFsep [hcat [pretty var, char '@', pretty pat], text ":", pretty ty]
  prettyPrec _ (VarPat var) = prettyBndr var
  prettyPrec _ (LitPat lit) = pretty lit
  prettyPrec p (InfixPat a cop _ b) = parensIf (p > 0) $
    myFsep [pretty a, pretty cop, pretty b]
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
  prettyPrec _ (WildPat _) = char '_'
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

-- instance IsPostTc p => Sorted Lit (PolyType p) where
--   sortOf (IntLit lit) | lit >= 0  = monoTy $ natTy
--                       | otherwise = monoTy $ intTy

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

instance (Ge p Tc, VAR p ~ Var p, TyVAR p ~ TyVar, TyCON p ~ TyCon p) => Sorted BuiltinCon (Sigma p) where
  sortOf UnitCon  = unitTy
  sortOf FalseCon = boolTy
  sortOf TrueCon  = boolTy
  sortOf NilCon   = forallTy [a_tv] $ ListTy a
    where a_nm = mkUsrName (mkOccName TyVarNS "a") a_uniq
          a_uniq = -1001
          a_tv = TyV a_nm typeKi False
          a = VarTy a_tv
  sortOf ConsCon  = forallTy [a_tv] $ a --> ListTy a --> ListTy a
    where a_nm = mkUsrName (mkOccName TyVarNS "a") a_uniq
          a_uniq = -1002
          a_tv = TyV a_nm typeKi False
          a = VarTy a_tv

instance (Ge p Tc, VAR p ~ Var p, TyVAR p ~ TyVar, TyCON p ~ TyCon p) => Sorted (Con p) (Sigma p) where
  sortOf (UserCon ucon)    = sortOf ucon
  sortOf (BuiltinCon bcon) = sortOf bcon

instance Pretty (NAME p) => Pretty (Con p) where
  pretty (UserCon name)    = pretty name
  pretty (BuiltinCon bcon) = pretty bcon

ppPrefixCon :: Pretty (NAME p) => Con p -> Doc
ppPrefixCon (BuiltinCon ConsCon) = text "(::)"
ppPrefixCon con                  = pretty con

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

instance (Ge p Tc, VAR p ~ Var p, TyVAR p ~ TyVar, TyCON p ~ TyCon p) => Sorted Op (Sigma p) where
  sortOf (BoolOp bop) = sortOf bop
  sortOf (IntOp iop)  = sortOf iop
  sortOf (ConOp bcon) = sortOf bcon

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

instance (Ge p Tc, VAR p ~ Var p, TyVAR p ~ TyVar, TyCON p ~ TyCon p) => Sorted BoolOp (Sigma p) where
  sortOf NotB = boolTy --> boolTy
  sortOf OrB = boolTy --> boolTy --> boolTy
  sortOf AndB = boolTy --> boolTy --> boolTy
  sortOf ImpB = boolTy --> boolTy --> boolTy
  sortOf IffB = boolTy --> boolTy --> boolTy
  sortOf EqB  = forallTy [a_tv] $ a --> a --> boolTy
    where a_nm = mkUsrName (mkOccName TyVarNS "a") a_uniq
          a_uniq = -2001
          a_tv = TyV a_nm typeKi False
          a = VarTy a_tv
  sortOf NeqB  = forallTy [a_tv] $ a --> a --> boolTy
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
    deriving(Eq,Ord)

  -- / and % could be more specific but that would introduce a mutually recursive
  -- dependency between both of them: that should be OK since they are built-in, but
  -- since the language does not allow you to do that.. we don't allow that as well.
  -- we may provide some assumed theorems, for instance
  -- theorem div_mod = forall n m, (n/m) * m + (n%m) == n
instance (Ge p Tc, VAR p ~ Var p, TyCON p ~ TyCon p) => Sorted IntOp (Sigma p) where
  sortOf NegI = intTy --> intTy
  sortOf AddI = intTy --> intTy --> intTy
  sortOf SubI = intTy --> intTy --> intTy
  sortOf MulI = intTy --> intTy --> intTy
  sortOf DivI = intTy
                            --> (varDom m intTy (Var m ./=. lit_0)
                            \--> intTy)
    where m = mkVar m_nm intTy
          m_nm = mkSysName (mkOccName VarNS "m") m_uniq
          m_uniq = -3002
  sortOf ModI = intTy
                            --> (varDom m intTy (Var m ./=. lit_0)
                            \--> intTy)
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

instance Pretty Op where
  pretty (BoolOp bop) = pretty bop
  pretty (IntOp iop)  = pretty iop
  pretty (ConOp cop)  = pretty cop

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

data Quantifier = ForallQ
                | ExistsQ
    deriving Eq

instance Pretty Quantifier where
  pretty ForallQ = text "forall"
  pretty ExistsQ = text "exists"

-- ** Constructors

lit_0 :: Exp p
lit_0 = Lit (IntLit 0)

app :: Exp p -> [Exp p] -> Exp p
app f args = foldl App f args

(.<.), (.<=.), (.>.), (.>=.) :: Exp p -> Exp p -> Prop p
x .<. y = InfixApp x (Op ltOp) y
x .<=. y = InfixApp x (Op leOp) y
x .>. y = InfixApp x (Op gtOp) y
x .>=. y = InfixApp x (Op geOp) y

(.==.), (./=.) :: Exp p -> Exp p -> Prop p
x .==. y = InfixApp x (Op eqOp) y
x ./=. y = InfixApp x (Op neqOp) y

(.+.), (.-.), (.*.), (./.) :: Exp p -> Exp p -> Exp p
x .+. y = InfixApp x (Op addOp) y
x .-. y = InfixApp x (Op subOp) y
x .*. y = InfixApp x (Op mulOp) y
x ./. y = InfixApp x (Op divOp) y

-- * Types

typeOf :: Sorted a (Type c p) => a -> Type c p
typeOf = sortOf

-- | Rank-1 polymorphic types
-- data PolyType p = ForallTy (TyParams p) (Type p)

-- forallTy :: TyParams p -> Type p -> PolyType p
forallTy = ForallTy

-- monoTy :: Type p -> PolyType p
-- monoTy = ForallTy []

quantifiedTyVars :: Sigma p -> [TyVAR p]
quantifiedTyVars (ForallTy tvs _) = tvs
quantifiedTyVars _other           = []

data SIG
data TAU

type Sigma = Type SIG
type Tau   = Type TAU

tau2sigma :: Tau p -> Sigma p
tau2sigma = unsafeCoerce

tau2type :: Tau p -> Type c p
tau2type = unsafeCoerce

sigma2tau :: Sigma p -> Tau p
sigma2tau (ForallTy _ _) = error "bug sigma2tau"  -- FIX
sigma2tau ty             = unsafeCoerce ty


-- | Monomorphic types
data Type c p where
  -- | type variable
  VarTy :: TyVAR p -> Type c p
  -- | named type or type constructor
  ConTyIn :: Lt p Tc => TyCON p -> Type c p
  -- | application of a type constructor
  AppTyIn :: Lt p Tc => Tau p -> Tau p -> Type c p
  ConTy :: Ge p Tc => TyCON p -> [Tau p] -> Type c p
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
  MetaTy :: MetaTyVar -> Type c Tc
  -- | rank-1 polymorphic type
  ForallTy :: TyParams p -> Tau p -> Sigma p

  -- NB: The @Dom Nothing ty (Just prop)@ is pointless
data Dom p = Dom {
               domMbPat  :: Maybe (Pat p)
             , domType   :: Tau p
             , domMbProp :: Maybe (Prop p)
             }

dom2type :: Ge p Tc => Dom p -> Type c p
dom2type (Dom mbPat ty mbProp) = predTy pat ty mbProp
  where pat = maybe (WildPat (PostTc ty)) id mbPat

type Range = Tau

type PostTcType p = PostTc p (Tau p)
type PostTcTypes p = PostTc p [Tau p]

  -- (args,result)
splitFunTy :: Tau p -> ([Dom p],Tau p)
splitFunTy (FunTy a t) = (a:args,res)
  where (args,res) = splitFunTy t
splitFunTy ty = ([],ty)

funTyArity :: Tau p -> Int
funTyArity ty = length args
  where (args,res) = splitFunTy ty

-- | Removes outermost predicate-types
mu_0 :: Tau p -> Tau p
mu_0 (PredTy _ ty _) = mu_0 ty
mu_0 ty              = ty

isSynTy :: (Ge p Tc, VAR p ~ Var p, TyCON p ~ TyCon p) => Type c p -> Bool
isSynTy (ConTy SynTyCon{} _) = True
isSynTy _other               = False

isMetaTy :: Type c Tc -> Bool
isMetaTy (MetaTy _) = True
isMetaTy _other     = False

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
--     , tyConParams :: [TyVar]
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
--             , tyConParams = []
            }
boolTyCon = AlgTyCon {
              tyConName   = BuiltinTyCon BoolTyCon
--             , tyConParams = []
            }
intTyCon  = AlgTyCon {
              tyConName   = BuiltinTyCon IntTyCon
--             , tyConParams = []
            }
natTyCon  = SynTyCon {
              tyConName   = BuiltinTyCon NatTyCon
            , tyConParams = []
            , synTyConRhs = predTy (VarPat n) intTy (Just $ (Var n) .>=. (Lit (IntLit 0)))
            }
  where n = mkVar n_nm intTy
        n_nm = mkSysName (mkOccName VarNS "n") n_uniq
        n_uniq = -4001

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
                 , mtvRef  :: IORef (Maybe (Tau Tc))
                 }

instance Eq MetaTyVar where
  (==) = (==) `on` mtvName

instance Ord MetaTyVar where
  compare = compare `on` mtvName

instance Named MetaTyVar where
  nameOf = mtvName

instance Sorted MetaTyVar Kind where
  sortOf = mtvKind

instance Pretty MetaTyVar where
  pretty (MetaTyV name _ _) = char '?' <> pretty name

instTyVar :: (MonadUnique m, MonadIO m) => TyVar -> m (Type c Tc)
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

newMetaTy :: (MonadUnique m, MonadIO m) => String -> Kind -> m (Tau Tc)
newMetaTy str kind = liftM MetaTy $ newMetaTyVar str kind

-- ** Constructors

infixr \-->, -->, ++>

appTyIn :: (Lt p Tc, TyCON p ~ TyName p) => TyName p -> [Tau p] -> Type c p
appTyIn tc args = unsafeCoerce $ foldl AppTyIn (ConTyIn tc) args

(\-->) :: Dom p -> Range p -> Type c p
(\-->) = FunTy

(-->) :: Tau p -> Tau p -> Type c p
dom --> ran = Dom Nothing dom Nothing \--> ran

funTy :: [Dom p] -> Range p -> Type c p
funTy doms rang = unsafeCoerce $ foldr (\-->) rang doms

type2dom :: Tau p -> Dom p
type2dom ty = Dom Nothing ty Nothing

dom :: Pat p -> Tau p -> Prop p -> Dom p
dom pat ty prop = Dom (Just pat) ty (Just prop)


varDom :: VAR p -> Tau p -> Prop p -> Dom p
varDom x ty prop = Dom (Just (VarPat x)) ty (Just prop)

patternDom :: Pat p -> Tau p -> Dom p
patternDom (WildPat _) ty = Dom Nothing ty Nothing
patternDom pat     ty = Dom (Just pat) ty Nothing

vpatDom :: VAR p -> Tau p -> Dom p
vpatDom x = patternDom (VarPat x)

patternTy :: Pat p -> Tau p -> Type c p
patternTy (WildPat _) ty = unsafeCoerce ty
patternTy (VarPat _)  ty = unsafeCoerce ty
patternTy pat         ty = PredTy pat ty Nothing

predTy :: Pat p -> Tau p -> Maybe (Prop p) -> Type c p
predTy pat ty Nothing = patternTy pat ty
predTy pat ty prop    = PredTy pat ty prop

unitTy, boolTy, intTy, natTy :: (Ge p Tc, VAR p ~ Var p, TyCON p ~ TyCon p) => Type c p
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

funKi :: [Kind] -> Kind -> Kind
funKi doms rang =  foldr (++>) rang doms
