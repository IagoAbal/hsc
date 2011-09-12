{-# LANGUAGE TypeSynonymInstances,
             FlexibleContexts,
             GeneralizedNewtypeDeriving
             #-}

module H.SrcContext where

import H.Syntax
import H.SrcLoc
import H.Pretty


-- * Source context

type CtxtDescr = Doc

data SrcContext
  = SrcContext {
      contextLoc    :: SrcLoc
    , contextDescr  :: CtxtDescr
    , isPropContext :: Bool
    }

class Monad m => MonadContext m where
  getContext    :: m SrcContext
  inContext     :: CtxtDescr -> m a -> m a
  inContextAt   :: SrcLoc -> CtxtDescr -> m a -> m a
  inPropContext :: m a -> m a
  popContext    :: m a -> m a

-- inContextMaybeAt :: MonadContext m => Maybe SrcLoc -> CtxtDescr -> m a -> m a
-- inContextMaybeAt Nothing    = inContext
-- inContextMaybeAt (Just loc) = inContextAt loc

-- * Predefined contexts

inTypeDeclCtxt :: MonadContext m => SrcLoc -> Doc -> m a -> m a
inTypeDeclCtxt loc pp_name = inContextAt loc (text "In type declaration" <+> pp_name)

inDataDeclCtxt :: MonadContext m => SrcLoc -> Doc -> m a -> m a
inDataDeclCtxt loc pp_name = inContextAt loc (text "In data declaration" <+> pp_name)

inConDeclCtxt :: MonadContext m => SrcLoc -> Doc -> m a -> m a
inConDeclCtxt loc pp_name = inContextAt loc (text "In data constructor declaration" <+> pp_name)

inFunBindCtxt :: MonadContext m => Doc -> m a -> m a
inFunBindCtxt pp_name = inContext (text "In the definition of" <+> pp_name)

inPatBindCtxt :: MonadContext m => SrcLoc -> Doc -> m a -> m a
inPatBindCtxt loc pp_pat = inContextAt loc (text "In pattern binding" <+> pp_pat)

inFunMatchCtxt :: MonadContext m => SrcLoc -> m a -> m a
inFunMatchCtxt loc = inContextAt loc (text "In function equation")

inGoalDeclCtxt :: MonadContext m => SrcLoc -> GoalType -> Doc -> m a -> m a
inGoalDeclCtxt loc gtype pp_name = inContextAt loc (text "In" <+> pretty gtype <+> pp_name)

inLambdaAbsCtxt :: (MonadContext m, PrettyNames p) => SrcLoc -> [Pat p] -> m a -> m a
inLambdaAbsCtxt loc pats = inContextAt loc (text "In lambda abstraction: \\" <+> (myFsep $ map pretty pats) <+> text "-> ...")

inCaseAltCtxt :: (MonadContext m, PrettyNames p) => SrcLoc -> Pat p -> m a -> m a
inCaseAltCtxt loc pat = inContextAt loc (text "In the case alternative" <+> ppQuot pat)

inGuardedRhsCtxt :: MonadContext m => SrcLoc -> m a -> m a
inGuardedRhsCtxt loc = inContextAt loc (text "In guarded alternative")

inExprCtxt :: (MonadContext m, PrettyNames p) => Exp p -> m a -> m a
inExprCtxt expr = inContext (text "In expression:" <+> pretty expr)

inCoercExprCtxt :: MonadContext m => SrcLoc -> m a -> m a
inCoercExprCtxt loc = inContextAt loc (text "In type coercion")

inQPExprCtxt :: (MonadContext m, PrettyNames p) => Quantifier -> [Pat p] -> m a -> m a
inQPExprCtxt qt pats = inContext (text "In formula:" <+> myFsep (pretty qt : map pretty pats) <+> comma <+> text "...")

inIteExprCtxt :: (MonadContext m, PrettyNames p) => Prop p -> m a -> m a
inIteExprCtxt guard = inContext (text "In expression:" <+> text "if" <+> pretty guard <+> text "then ... else ...")

inIfExprCtxt :: MonadContext m => m a -> m a
inIfExprCtxt = inContext (text "In expression:" <+> text "if" <+> text "| ...")

inCaseExprCtxt :: (MonadContext m, PrettyNames p) => Prop p -> m a -> m a
inCaseExprCtxt scrut = inContext (text "In expression:" <+> text "case" <+> pretty scrut <+> text "of ...")

inTypeCtxt :: (MonadContext m, PrettyNames p) => Type c p -> m a -> m a
inTypeCtxt ty = inContext (text "In type:" <+> pretty ty)
