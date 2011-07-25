{-# LANGUAGE KindSignatures,
             FlexibleInstances,
             TypeSynonymInstances,
             NamedFieldPuns,
             PatternGuards,
             GADTs,
             TypeOperators
             #-}

-- | One-shot substitution
-- It allows several *independent* substitutions to be performed in parallel.
module H.Subst1
  ( Subst1
  , mkSubst1
  , Subst(..)
  ) where

import H.Syntax
import H.Phase

import Sorted
import Unique( MonadUnique )

import Control.Monad
import Data.Map( Map )
import qualified Data.Map as Map
import Data.Set( Set )
import qualified Data.Set as Set


-- * One-shot substition

  
data Subst1 = Subst1 {
                substEnv   :: Map (Var Tc) (Exp Tc)
                -- | variables in scope,
                -- overapproximating the set of free variables
              , substScope :: Set (Var Tc)
              }

mkSubst1 :: [(Var Tc,Exp Tc)] -> Set (Var Tc) -> Subst1
mkSubst1 envList scope = Subst1 (Map.fromList envList) scope

class Subst t where
  subst :: MonadUnique m => Subst1 -> t -> m t

class SubstBndr b where
  substBndr :: MonadUnique m => Subst1 -> b -> m (b,Subst1)


instance Subst t => Subst (Maybe t) where
  subst s Nothing  = return Nothing
  subst s (Just t) = liftM Just $ subst s t

instance Subst t => Subst [t] where
  subst s ts = mapM (subst s) ts

instance SubstBndr b => SubstBndr (Maybe b) where
  substBndr s Nothing  = return (Nothing,s)
  substBndr s (Just b) = do (b',s') <- substBndr s b
                            return (Just b',s')

-- Substitution for multi-binders
-- It assumes that in b1,b2,...,bn a bi may depend on a bj if j < i,
-- but it is also valid if there is no dependency.
instance SubstBndr b => SubstBndr [b] where
  substBndr s bs = do (bs'_rev,s') <- foldM go ([],s) bs
                      let bs' = reverse bs'_rev
                      return (bs',s')
    where go (bs',s) b = do (b',s') <- substBndr s b
                            return (b':bs',s')

instance SubstBndr (Var Tc) where
  substBndr (Subst1{substEnv,substScope}) var
    = if var `Set.member` substScope
            -- @var@ may capture some variable 
         then do var' <- newVarFrom var
                 let env'   = Map.insert var (Var var') substEnv
                 let scope' = Set.insert var' substScope
                 return (var',Subst1 env' scope')
            -- @var@ will not capture any variable
         else do let env'   = Map.delete var substEnv
                 let scope' = Set.insert var substScope
                 return (var,Subst1 env' scope')

instance SubstBndr (Decl s Tc) where
  substBndr s (TypeDecl loc tynm tyargs ty)
    = do ty' <- subst s ty
         return (TypeDecl loc tynm tyargs ty', s)
  substBndr s (DataDecl loc tynm tyargs cons)
    = do cons' <- subst s cons
         return (DataDecl loc tynm tyargs cons',s)
  substBndr s (TypeSig loc funs polyty)
    = do polyty' <- subst s polyty
         return (TypeSig loc funs polyty',s)
  substBndr s (FunBind NonRec fun matches)
    = do matches' <- subst s matches  -- non-recursive bindings
         (fun',s') <- substBndr s fun
         return (FunBind NonRec fun' matches',s')
  substBndr s (FunBind Rec fun matches)
    = do (fun',s') <- substBndr s fun
         matches' <- subst s' matches  -- recursive bindings
         return (FunBind Rec fun' matches',s')
  substBndr s (PatBind loc NonRec pat rhs)
    = do rhs' <- subst s rhs    -- non-recursive bindings
         (pat',s') <- substBndr s pat
         return (PatBind loc NonRec pat' rhs',s')
  substBndr s (PatBind loc Rec pat rhs)
    = do (pat',s') <- substBndr s pat
         rhs' <- subst s' rhs    -- recursive bindings
         return (PatBind loc Rec pat' rhs',s')
  substBndr s (GoalDecl loc gname gtype ptctyparams prop)
    = do prop' <- subst s prop
         return (GoalDecl loc gname gtype ptctyparams prop',s)

instance Subst (Decl s Tc) where
  subst s decl = liftM fst $ substBndr s decl

instance Subst (ConDecl Tc) where
  subst s (ConDecl loc con args)
    = do (args',_s') <- substBndr s args
         return (ConDecl loc con args')

instance Subst (Match Tc) where
  subst s (Match loc pats rhs)
    = do (pats',s') <- substBndr s pats
         liftM (Match loc pats') (subst s' rhs)

instance Subst (Exp Tc) where
  subst s@(Subst1{substEnv}) (Var x@(V name ty))
    | Just e <- Map.lookup x substEnv  = return e
    | otherwise                        = do ty' <- subst s ty
                                            return $ Var (V name ty')
  subst s con@(Con _) = return con
  subst s lit@(Lit _) = return lit
  subst s (PrefixApp op e) =  PrefixApp op `liftM` subst s e
  subst s (InfixApp e1 op e2) = do e1' <- subst s e1
                                   e2' <- subst s e2
                                   return $ InfixApp e1' op e2'
  subst s (App f n) = liftM2 App (subst s f) (subst s n)
  subst s (TyApp e tys) = liftM2 TyApp (subst s e) (subst s tys)
  subst s (Lam loc apats body)
    = do (apats',s') <- substBndr s apats
         body' <- subst s' body
         return $ Lam loc apats' body'
  subst s (TyLam tvs e) = TyLam tvs `liftM` subst s e
  subst s (Let decls body) = do (decls',s') <- substBndr s decls
                                liftM (Let decls') (subst s' body)
  subst s (Ite g t e) = liftM3 Ite (subst s g) (subst s t) (subst s e)
  subst s (If grhss) = liftM If $ subst s grhss
  subst s (Case e casety alts)
    = liftM3 Case (subst s e) (subst s casety) (subst s alts)
  subst s (Tuple es) = liftM Tuple $ subst s es
  subst s (List es) = liftM List $ subst s es
  subst s (Paren e) = liftM Paren $ subst s e
  subst s (LeftSection e op) = do e' <- subst s e
                                  return $ LeftSection e' op
  subst s (RightSection op e) = liftM (RightSection op) $ subst s e
  subst s (EnumFromTo e1 en) = liftM2 EnumFromTo (subst s e1) (subst s en)
  subst s (EnumFromThenTo e1 e2 en)
    = liftM3 EnumFromThenTo (subst s e1) (subst s e2) (subst s en)
  subst s (Coerc loc e ty) = liftM2 (Coerc loc) (subst s e) (subst s ty)
  subst s (QP q pats body) = do (pats',s') <- substBndr s pats
                                liftM (QP q pats') $ subst s' body

instance Subst (Rhs Tc) where
  subst s (Rhs grhs whr) = do (whr',s') <- substBndr s whr
                              grhs' <- subst s' grhs
                              return (Rhs grhs' whr')

instance Subst (GRhs Tc) where
  subst s (UnGuarded e)   = liftM UnGuarded $ subst s e
  subst s (Guarded grhss) = liftM Guarded (subst s grhss)

instance Subst (GuardedRhss Tc) where
  subst s (GuardedRhss pgrhss elserhs)
    = liftM2 GuardedRhss (subst s pgrhss) (subst s elserhs)

instance Subst (GuardedRhs Tc) where
  subst s (GuardedRhs loc g e) = liftM2 (GuardedRhs loc) (subst s g) (subst s e)

instance Subst (Else Tc) where
  subst s (Else loc e) = liftM (Else loc) $ subst s e
  subst s NoElse   = return NoElse

instance SubstBndr (Pat Tc) where
  substBndr s (VarPat var) = do (var',s') <- substBndr s var
                                return (VarPat var',s')
  substBndr s p@(LitPat _) = return (p,s)
  substBndr s (InfixPat p1 con p2)
    = do ([p1',p2'],s') <- substBndr s [p1,p2]
         return (InfixPat p1' con p2',s')
  substBndr s (ConPat con ps) = do (ps',s') <- substBndr s ps
                                   return (ConPat con ps',s')
  substBndr s (TuplePat ps) = do (ps',s') <- substBndr s ps
                                 return (TuplePat ps',s')
  substBndr s (ListPat ps) = do (ps',s') <- substBndr s ps
                                return (ListPat ps',s')
  substBndr s (ParenPat p) = substBndr s p
  substBndr s p@WildPat = return (p,s)
    -- See [SubstBndr.AsPat]
  substBndr s (AsPat v p) = do (p',s') <- substBndr s p
                               (v',s'') <- substBndr s' v
                               return (AsPat v' p',s'')


{- NOTE [SubstBndr.AsPat]
Since the renamer ensures that, for 'v@pat', 'v' is fresh w.r.t. FV('pat')
the order in which we call substBndr does not matter. But semantically,
we must remember that an @-pattern is translated by shifting the 'alias'
variable to the RHS as a let-binding, so to call substBndr over 'pat'
in first place is the 'most correct' way.
-}

instance Subst (Alt Tc) where
  subst s (Alt loc pat rhs) = do (pat',s') <- substBndr s pat
                                 liftM (Alt loc pat') $ subst s' rhs

instance Subst (PolyType Tc) where
  subst s (ForallTy tvs ty) = do ty' <- subst s ty
                                 return $ ForallTy tvs ty'

instance Subst (Type Tc) where
  subst s ty@(VarTy _) = return ty
  subst s ty@(ConTy _) = return ty
  subst s (AppTy ty1 ty2) = liftM2 AppTy (subst s ty1) (subst s ty2)
  subst s (PredTy pat ty mbProp)
    = do ty' <- subst s ty
         (pat',s') <- substBndr s pat
         liftM (PredTy pat' ty') $ subst s mbProp
  subst s (FunTy dom rang) = do (dom',s') <- substBndr s dom
                                liftM (FunTy dom') $ subst s' rang
  subst s (TupleTy tys) = do (tys',_s') <- substBndr s tys
                             return $ TupleTy tys'


instance SubstBndr (Dom Tc) where
  substBndr s (Dom mbPat ty mbProp)
    = do ty' <- subst s ty
         (mbPat',s') <- substBndr s mbPat
         mbProp' <- subst s' mbProp
         return (Dom mbPat' ty' mbProp',s')

instance Subst (PostTcType Tc) where
  subst s (PostTc ty) = liftM PostTc $ subst s ty


instance (SubstBndr b, Subst a) => SubstBndr (b ::: a) where
  substBndr s (b ::: a) = do a' <- subst s a
                             (b',s') <- substBndr s b
                             return (b' ::: a',s')
