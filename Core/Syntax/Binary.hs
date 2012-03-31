{-# LANGUAGE TemplateHaskell #-}

-- | Binary (de-)serialization for Core syntax
-- NB: Those 'Binary' insntaces are being generated through Template Haskell
module Core.Syntax.Binary where


import Core.Syntax.AST

import Data.Binary ( Binary(..), getWord8, putWord8 )
import Data.DeriveTH



$( derive makeBinary ''Var )
$( derive makeBinary ''TyVar )
$( derive makeBinary ''Decl )
$( derive makeBinary ''IsRec )
$( derive makeBinary ''ConDecl )
$( derive makeBinary ''Bind )
-- $( derive makeBinary ''Match )
$( derive makeBinary ''BuiltinCon )
$( derive makeBinary ''Con )
$( derive makeBinary ''Lit )
$( derive makeBinary ''Exp )
$( derive makeBinary ''OpExp )
$( derive makeBinary ''Op )
$( derive makeBinary ''IntOp )
$( derive makeBinary ''BoolOp )
$( derive makeBinary ''Rhs )
-- $( derive makeBinary ''GRhs )
-- $( derive makeBinary ''GuardedRhs )
-- $( derive makeBinary ''GuardedRhss )
$( derive makeBinary ''GoalType )
$( derive makeBinary ''Quantifier )
$( derive makeBinary ''BuiltinTyCon )
$( derive makeBinary ''Pat )
$( derive makeBinary ''Alt )
$( derive makeBinary ''TyName )
$( derive makeBinary ''TyCon )
$( derive makeBinary ''Type )
$( derive makeBinary ''Dom )
$( derive makeBinary ''Kind )
