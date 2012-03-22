{-# LANGUAGE NamedFieldPuns, FlexibleContexts #-}

module H.Typecheck.TCC where

import H.Syntax
import H.Phase
import Pretty
import H.Prop
import H.Message

import Data.Foldable ( toList )
import Data.Sequence ( Seq )
-- import qualified Data.Sequence as Seq


data TccHypoThing = ForAll [QVar Ti]
                  | LetIn [Bind Ti]
                  | Facts [Prop Ti]

instance Pretty TccHypoThing where
  pretty (ForAll qvs)
    = myFsep $ text "forall" : map pretty qvs
  pretty (LetIn binds)
    = text "let" <+> ppBody letIndent (map pretty binds)
  pretty (Facts props)
    = pretty $ conj props
    
type TccPropCtxt = Seq TccHypoThing

data TCC
  = CoercionTCC {
      tccSrcCtxt  :: !Message
    , tccPropCtxt :: TccPropCtxt
    , tccExpr     :: Exp Ti
    , tccActType  :: Sigma Ti
    , tccExpType  :: Sigma Ti
    }
  | CompletenessTCC {
      tccSrcCtxt  :: !Message
    , tccPropCtxt :: TccPropCtxt
    , tccProps    :: Prop Ti
    }

-- filterTCCs :: [TCC Ti] -> [TCC Ti]
-- filterTCCs tccs = filter (not . isTy2TyCoercion) tccs
--   where isTy2TyCoercion CoercionTCC{tccActType,tccExpType} = tccActType == tccExpType
--         isTy2TyCoercion _other                             = False

instance Pretty TCC where
  pretty (CoercionTCC srcCtxt propCtxt expr act_ty exp_ty)
    = brackets srcCtxt
    $$ (vcat $ map pretty $ toList propCtxt)
    $$ text "|------------------------------------------------------ (COERCION)"
    $$ pretty act_ty
    $$ text "~~" <+> pretty expr <+> text "~~>"
    $$ pretty exp_ty
  pretty (CompletenessTCC srcCtxt propCtxt prop)
    = brackets srcCtxt
    $$ (vcat $ map pretty $ toList propCtxt)
    $$ text "|------------------------------------------------------ (COMPLETENESS)"
    $$ pretty prop
