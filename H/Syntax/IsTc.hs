
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      :  H.Syntax.IsTc
-- Copyright   :  (c) Iago Abal 2011-2012
-- License     :  BSD3
--
-- Maintainer  :  Iago Abal, iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--

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
