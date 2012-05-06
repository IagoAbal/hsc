
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module H.Syntax.IsTc
  where

import H.Syntax.AST
import H.Syntax.Phase
import H.Syntax.Pretty ( PrettyNames )

import Name


      -- FIX this
class (Ge p Rn, Ge p Tc,
       VAR p ~ Var p, CON p ~ TcCon p,
       TyVAR p ~ TyVar, TyCON p ~ TyCon p,
       GoalNAME p ~ Name,
       PrettyNames p) => IsTc p where

instance IsTc Tc where
instance IsTc Ti where
