{-# LANGUAGE GADTs #-}

module H.Typecheck.Unify where

import H.Typecheck.TcM
import H.Typecheck.MetaTyVar
import H.Typecheck.Zonk

import H.Syntax
import H.Phase
import H.Pretty
import H.FreeVars
import H.Prop

import Data.Set ( Set )
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Error
import Data.Function ( on )


-- | A kappa type contains no dependency nor any reference to local
-- variables.
-- Importance: A meta-variable can only be instantiated with a kappa type.
kappaType :: Type Tc -> TcM (Type Tc)
kappaType ty@(VarTy _) = return ty
  -- 'kappaType' does not expand type synonyms, that is unifier's task.
kappaType (ConTy tc args) = liftM (ConTy tc) $ mapM kappaType args
-- kappaType ty@(ConTy _) = return ty
-- kappaType (AppTy t a) = liftM2 AppTy (kappaType t) (kappaType a)
kappaType (PredTy pat ty Nothing) = do
  ty' <- kappaType ty
  return (patternTy pat ty')
kappaType (PredTy pat ty (Just prop)) = do
  ty' <- kappaType ty
  gbl <- asks tcGblVars
    -- This is so easy because we have a no-shadowing representation
    -- otherwise we would have to keep track of any variable in scope
    -- because it may be shadowing a global variable.
  let valid p = (fvExp p Set.\\ bsPat pat) `Set.isSubsetOf` gbl
      mbprop' = filterProp valid prop
  return (predTy pat ty mbprop')
kappaType (FunTy d r) = liftM2 FunTy (kappaDom d) (kappaType r)
kappaType (ListTy a) = liftM ListTy $ kappaType a
kappaType (TupleTy ds) = liftM TupleTy $ mapM kappaDom ds
  -- 'kappaType' does not "go" into meta type variables,
  -- that is unifier's task.
kappaType ty@(MetaTy _) = return ty


  -- FIX I think kappa types should allow dependent types, because we may want to
  -- unify a metaty with a dependent type...
kappaDom :: Dom Tc -> TcM (Dom Tc)
kappaDom (Dom Nothing ty Nothing) = do
  ty' <- kappaType ty
  return (Dom Nothing ty' Nothing)
kappaDom (Dom (Just pat) ty mbprop) = do
  ty' <- kappaType $ predTy pat ty mbprop
  return (Dom Nothing ty' Nothing)

  

-- unifyKind :: Kind -> Kind -> TcM ()
-- unifyKind TypeKi TypeKi = return ()
-- unifyKind (FunKi k1 k2) (FunKi k1' k2') = do
--   unifyKind k1 k1'
--   unifyKind k2 k2'
-- unifyKind k1 k2 = error "Cannot unifyKappa kinds"


(~>) :: Type Tc -> Type Tc -> TcM ()
(~>) = unify

    -- !! no expression is needed because we don't generate TCCs now
unify :: Type Tc      -- ^ actual type
          -> Type Tc  -- ^ expected type
          -> TcM ()
unify ty1 ty2 = do
  ty1' <- kappaType ty1
  ty2' <- kappaType  ty2
  unifyKappa ty1' ty2'

unifyKappa :: Type Tc      -- ^ actual type
          -> Type Tc  -- ^ expected type
          -> TcM ()
  -- fix, VarTy could be a skolem tyvar as well...
-- unifyKappa ty1@(VarTy _) ty2@(VarTy _) = error "Panic! Bound type variables found during unification"

unifyKappa (VarTy tv1) (VarTy tv2) | tv1 == tv2 = return ()

unifyKappa (MetaTy mtv1) (MetaTy mtv2) | mtv1 == mtv2 = return ()

unifyKappa (MetaTy mtv1) ty2 = unifyVar LeftToRight mtv1 ty2
unifyKappa ty1 (MetaTy mtv2) = unifyVar RightToLeft mtv2 ty1

unifyKappa (FunTy d1 r1) (FunTy d2 r2) = do
  unifyKappa (dom2type d1) (dom2type d2)
  unifyKappa r1 r2
unifyKappa (ListTy ty1) (ListTy ty2) = unifyKappa ty1 ty2
unifyKappa (TupleTy ds1) (TupleTy ds2)
  | length ds1 == length ds2 = zipWithM_ (unifyKappa `on` dom2type) ds1 ds2

  -- See [Unifying predicate types]
unifyKappa (PredTy _ ty1 _) ty2 = unifyKappa ty1 ty2
unifyKappa ty1 (PredTy _ ty2 _) = unifyKappa ty1 ty2

unifyKappa ty1 ty2 | isSynTy ty1 = do
  Just ty1' <- expandSyn ty1
  unify ty1' ty2
  
unifyKappa ty1 ty2 | isSynTy ty2 = do
  Just ty2' <- expandSyn ty2
  unify ty1 ty2'

unifyKappa (ConTy tc1 args1) (ConTy tc2 args2)
  | tc1 == tc2 = zipWithM_ unifyKappa args1 args2

unifyKappa ty1 ty2
  = throwError $ text "Cannot unify" <+> pretty ty1 <+> text "with" <+> pretty ty2


{- Note [Unifying predicate types]

...

The order of equations is important, consider the following example:
  { p : ?a  | P } ~> { q : ?b | Q }

  - If we "drop" the first predicate type then we get the substitution
      a? = { q : ?b | Q }
    so in the VC phase we will find that { p : ?a  | P } is trivially
    coerced to a?.
  - If we "drop" the second predicate type in first place then we get
    the substitution
      b? = { p : ?a  | P }
    and to coerce b? to { q : ?b | Q } could not be possible.

In short, it is crucial to keep the expected type untouched as long as
possible in order to get the better substitution.
-}

data Direction = LeftToRight    -- ~>
               | RightToLeft    -- <~


flipByDirection :: Direction -> (a -> a -> b) -> (a -> a -> b)
flipByDirection LeftToRight = id
flipByDirection RightToLeft = flip

unifyVar :: Direction -> MetaTyVar -> Type Tc -> TcM ()
unifyVar dir mtv ty = traceDoc (text "unifyVar mtv=" <+> pretty mtv <+> text "ty=" <+> pretty ty) $ do
  mb_ty1 <- readMetaTyVar mtv
  case mb_ty1 of
      Nothing  -> do
--         ty_z <- zonkType ty
        traceDoc (text "unifyVar by unifyUnboundVar") $ do
        unifyUnboundVar dir mtv ty (mtvType ty)
      Just ty1 -> traceDoc (text "unifyVar by unifyKappa ty1=" <+> pretty ty1) $ flipByDirection dir unifyKappa ty1 ty

unifyUnboundVar :: Direction -> MetaTyVar -> Type Tc -> Set MetaTyVar -> TcM ()
unifyUnboundVar dir mtv1 ty@(MetaTy mtv2) ty_mtvs = traceDoc (text "unifyUnboundVar mtv1=" <+> pretty mtv1 <+> text "mtv2=" <+> pretty mtv2) $ do
  mb_ty2 <- readMetaTyVar mtv2
  case mb_ty2 of
      Nothing  -> writeMetaTyVar mtv1 ty
      Just ty2 -> flipByDirection dir unifyKappa (MetaTy mtv1) ty2
unifyUnboundVar dir mtv (PredTy _ ty1 _) ty_mtvs
  | mtv `Set.member` ty_mtvs = flipByDirection dir unifyKappa (MetaTy mtv) ty1
unifyUnboundVar dir mtv ty ty_mtvs
  | mtv `Set.member` ty_mtvs = error "occurs check" -- fix
  | otherwise                = writeMetaTyVar mtv ty


unifyFun :: Type Tc -> TcM (Dom Tc,Range Tc)
unifyFun ty = do
  ty_hz <- headZonkType ty
  case ty_hz of
    FunTy dom rang  -> return (dom,rang)
      -- important !
    PredTy _ _ _    -> unifyFun (mu_0 ty_hz)
    MetaTy mtv      -> do
      s <- newMetaTy "s" typeKi
      t <- newMetaTy "t" typeKi
      let funty@(FunTy dom rang) = s --> t
      writeMetaTyVar mtv funty
      return (dom,rang)
    other           -> error "not a function type" -- fix

unifyFuns :: Int -> Type Tc -> TcM ([Dom Tc],Range Tc)
unifyFuns 0 ty = return ([],ty)
unifyFuns n ty = do
  (d,r) <- unifyFun ty
  (ds,resty) <- unifyFuns (n-1) r
  return (d:ds,resty)
