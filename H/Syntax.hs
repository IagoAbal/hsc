
-- |
-- Module      :  H.Syntax
-- Copyright   :  (c) Iago Abal 2011-2012
-- License     :  BSD3
--
-- Maintainer  :  Iago Abal, iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Syntax of H!
-- Abstract syntax and related stuff.

module H.Syntax
  ( module H.Syntax.AST
  , module H.Syntax.Expr
  , module H.Syntax.FreeVars
  , module H.Syntax.IsTc
  , module H.Syntax.Pattern
  , module H.Syntax.Phase
  , module H.Syntax.Pretty
  , module H.Syntax.Subst1
  , module H.Syntax.Type
  ) where


import H.Syntax.AST
import H.Syntax.Expr
import H.Syntax.FreeVars
import H.Syntax.IsTc
import H.Syntax.Pattern
import H.Syntax.Phase
import H.Syntax.Pretty
import H.Syntax.Subst1
import H.Syntax.Type
