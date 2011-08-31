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


-- | A kappa type contains no reference to local variables.
-- Importance: A meta-variable can only be instantiated with a kappa type.
kappaType :: Type Tc -> TcM (Type Tc)
kappaType ty = do
  gbl_vars <- asks tcGblVars
  return $ go gbl_vars ty
  where
      go :: Set (Var Tc)  -- valid variables
            -> Type Tc -> Type Tc
      go _vv ty@(VarTy _)    = ty
      go  vv (ConTy tc args) = ConTy tc $ map (go vv) args
      go  vv (PredTy pat ty Nothing) = patternTy pat (go vv ty)
      go  vv (PredTy pat ty (Just prop))
        = predTy pat (go vv ty) (go_prop vv_prop prop)
        where vv_prop = vv `Set.union` bsPat pat
      go vv (FunTy d r) = FunTy d' $ go vv' r
        where (d',vv') = go_dom vv d
      go vv (ListTy a) = ListTy $ go vv a
      go vv (TupleTy ds) = TupleTy $ go_doms vv ds
        -- 'kappaType' does not "go" into meta type variables,
        -- that is unifier's task.
      go vv ty@(MetaTy _) = ty
      go_prop :: Set (Var Tc) -> Prop Tc -> Maybe (Prop Tc)
      go_prop vv prop
        = filterProp valid prop
          -- This is so easy because we have a no-shadowing representation
          -- otherwise we would have to keep track of any variable in scope
          -- because it may be shadowing a global variable.
        where valid :: Prop Tc -> Bool
              valid p = fvExp p `Set.isSubsetOf` vv
      go_dom :: Set (Var Tc) -> Dom Tc -> (Dom Tc,Set (Var Tc))
      go_dom vv (Dom Nothing ty Nothing) = (Dom Nothing (go vv ty) Nothing,vv)
      go_dom vv (Dom (Just pat) ty Nothing)
        = (Dom (Just pat) (go vv ty) Nothing,vv `Set.union` bsPat pat)
      go_dom vv (Dom (Just pat) ty (Just prop))
        = (Dom (Just pat) (go vv ty) (go_prop vv' prop),vv')
        where vv' = vv `Set.union` bsPat pat
      go_doms :: Set (Var Tc) -> [Dom Tc] -> [Dom Tc]
      go_doms _vv [] = []
      go_doms  vv (d:ds) = d' : go_doms vv' ds
        where (d',vv') = go_dom vv d



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
  unify r1 r2
unifyKappa (ListTy ty1) (ListTy ty2) = unifyKappa ty1 ty2
unifyKappa (TupleTy ds1) (TupleTy ds2)
  | length ds1 == length ds2 = zipWithM_ (unify `on` dom2type) ds1 ds2

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
