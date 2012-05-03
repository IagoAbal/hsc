{-# LANGUAGE NamedFieldPuns,
             FlexibleContexts,
             TypeFamilies,
             RankNTypes,
             ScopedTypeVariables,
             GADTs
             #-}

module H.Typecheck.TcM where

import H.Syntax
import H.Syntax.FreeVars
import H.Phase
import Pretty
import H.Monad
import qualified H.Subst1 as Subst1

import Name

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Reader
import Data.IORef
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set


type TcM = H TcEnv () ()

data TcEnv
  = TcEnv {
      tcGblVars  :: Set (Var Tc)
    , tcVarEnv   :: Map Name (Var Tc)
    , tcTyVarEnv :: Map Name TyVar
    , tcTyConEnv :: Map (TyName Rn) (TyCon Tc)
    , tcConEnv   :: Map (Con Rn) (TcCon Tc)
    }

emptyTcEnv :: TcEnv
emptyTcEnv = TcEnv Set.empty Map.empty Map.empty
                (Map.fromList [(BuiltinTyCon UnitTyCon,unitTyCon)
                              ,(BuiltinTyCon BoolTyCon,boolTyCon)
                              ,(BuiltinTyCon IntTyCon,intTyCon)
                              ,(BuiltinTyCon NatTyCon,natTyCon)])
                (Map.fromList [(unitCon,tcUnitCon)
                              ,(falseCon,tcFalseCon)
                              ,(trueCon,tcTrueCon)
                              ,(nilCon,tcNilCon)
                              ,(consCon,tcConsCon)])

lookupTyCon :: TyName Rn -> TcM (TyCon Tc)
lookupTyCon tn = do
  tyConEnv <- asks tcTyConEnv
  case Map.lookup tn tyConEnv of
      Just tc -> return tc
      Nothing -> error $ "lookupTyCon tn=" ++ prettyPrint tn ++ " tyConEnv=" ++ concatMap (prettyPrint . fst) (Map.toList tyConEnv)


lookupVar :: Name -> TcM (Var Tc)
lookupVar n = do
  varEnv <- asks tcVarEnv
  case Map.lookup n varEnv of
      Just v  -> return v
      Nothing -> error $ "lookupVar  n=" ++ prettyPrint n ++ " varEnv=" ++ concatMap (prettyPrint . fst) (Map.toList varEnv)

lookupTyVar :: Name -> TcM TyVar
lookupTyVar n = do
  tyVarEnv <- asks tcTyVarEnv
  case Map.lookup n tyVarEnv of
      Just tv -> return tv
      Nothing -> error "lookupTyVar"

lookupCon :: Con Rn -> TcM (TcCon Tc)
lookupCon con = do
  conEnv <- asks tcConEnv
  case Map.lookup con conEnv of
      Just con' -> return con'
      Nothing   -> error "lookupCon"

addGlobalVars :: [Var Tc] -> TcM a -> TcM a
addGlobalVars vars = local (\env@TcEnv{tcGblVars} -> env{tcGblVars = Set.union tcGblVars vars_set})
  where vars_set = Set.fromList vars

extendVarEnv :: [(Name,Var Tc)] -> TcM a -> TcM a
extendVarEnv envl = local (\env@TcEnv{tcVarEnv} -> env{tcVarEnv = Map.union venv' tcVarEnv})
  where venv' = Map.fromList envl

extendTyVarEnv :: [(Name,TyVar)] -> TcM a -> TcM a
extendTyVarEnv envl = local (\env@TcEnv{tcTyVarEnv} -> env{tcTyVarEnv = Map.union tvenv' tcTyVarEnv})
  where tvenv' = Map.fromList envl
  
extendTyConEnv :: [(TyName Rn,TyCon Tc)] -> TcM a -> TcM a
extendTyConEnv envl = local (\env@TcEnv{tcTyConEnv} -> env{tcTyConEnv = Map.union tcenv' tcTyConEnv})
  where tcenv' = Map.fromList envl

extendConEnv :: [(Con Rn,TcCon Tc)] -> TcM a -> TcM a
extendConEnv envl = local (\env@TcEnv{tcConEnv} -> env{tcConEnv = Map.union cenv' tcConEnv})
  where cenv' = Map.fromList envl

getVarScope :: TcM (Set (Var Tc))
getVarScope = liftM (Set.fromList . Map.elems) $ asks tcVarEnv

getTyVarScope :: TcM (Set TyVar)
getTyVarScope = liftM (Set.fromList . Map.elems) $ asks tcTyVarEnv

substExp :: [(Var Tc,Exp Tc)] -> [(TyVar,Tau Tc)] -> Exp Tc -> TcM (Exp Tc)
substExp var_env tyvar_env exp = do
  var_scope <- getVarScope
  tyvar_scope <- getTyVarScope
  let subst1 = Subst1.mkSubst1 var_env tyvar_env var_scope tyvar_scope
  Subst1.substExp subst1 exp

substMatches :: [(Var Tc,Exp Tc)] -> [(TyVar,Tau Tc)] -> [Match Tc] -> TcM [Match Tc]
substMatches var_env tyvar_env matches = do
  var_scope <- getVarScope
  tyvar_scope <- getTyVarScope
  let subst1 = Subst1.mkSubst1 var_env tyvar_env var_scope tyvar_scope
  Subst1.substMatches subst1 matches

substType :: [(Var Tc,Exp Tc)] -> [(TyVar,Tau Tc)] -> Type c Tc -> TcM (Type c Tc)
substType var_env tyvar_env ty = do
  var_scope <- getVarScope
  tyvar_scope <- getTyVarScope
  let subst1 = Subst1.mkSubst1 var_env tyvar_env var_scope tyvar_scope
  Subst1.substType subst1 ty


getEnvTypes :: TcM [Sigma Tc]
getEnvTypes = liftM (map varType . Set.toList) getVarScope

-- instantiate :: Exp Tc -> PolyType Tc -> TcM (Exp Tc,Type Tc)
--   -- short-cut for mono-types
-- instantiate e (ForallTy []  ty) = return (e,ty)
-- instantiate e (ForallTy tvs ty) = do
--   mtys <- mapM instTyVar tvs
--   let e' = TyApp e mtys
--   ty' <- substType [] (zip tvs mtys) ty
--   return (e',ty')

instantiate :: Sigma Tc -> TcM (Tau Tc,[Tau Tc])
instantiate (ForallTy tvs ty) = do
  mtys <- mapM instTyVar tvs
  ty' <- substType [] (zip tvs mtys) ty
  return (ty',mtys)
instantiate ty = return (sigma2tau ty,[])

instantiateExp :: Exp Tc -> Sigma Tc -> TcM (Exp Tc,Tau Tc)
instantiateExp exp ty = do
  (ty',tyargs) <- instantiate ty
  return (tyApp exp tyargs,ty')

skolemise :: Sigma Tc -> TcM ([TyVar], Tau Tc)
skolemise (ForallTy tvs ty) = do
  tvs_sk <- mapM skoTyVar tvs
  let tys_sk = map VarTy tvs_sk
  ty' <- substType [] (zip tvs tys_sk) ty
  return (tvs_sk,ty')
skolemise ty = return ([],sigma2tau ty)

readMetaTyVar :: MonadIO m => MetaTyVar -> m (Maybe (Tau Tc))
readMetaTyVar = liftIO . readIORef . mtvRef

writeMetaTyVar :: MonadIO m => MetaTyVar -> Tau Tc -> m ()
writeMetaTyVar MetaTyV{mtvRef} = liftIO . writeIORef mtvRef . Just
  -- for debugging
-- writeMetaTyVar mtv@MetaTyV{mtvRef} ty =
--   traceDoc (text "writeMetaTyVar mtv=" <+> pretty mtv <+> text "ty=" <+> pretty ty) $ do
--     liftIO $ writeIORef mtvRef (Just ty)
