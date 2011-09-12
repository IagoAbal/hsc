{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module H.Message where

import H.Pretty
import H.SrcLoc ( SrcLoc )
import H.SrcContext ( CtxtDescr, SrcContext(..) )

import Control.Monad.Error.Class( Error(..) )


-- * Message

type Message = Doc


mkLocMessage :: SrcLoc -> Message -> Message
mkLocMessage loc msg = hang loc_pp 2 msg
  where loc_pp = pretty loc <> char ':'

addMessageContext :: CtxtDescr -> Message -> Message
addMessageContext ctxt msg = msg $$ ctxt

contextualizeMessage :: SrcContext -> Message -> Message
contextualizeMessage (SrcContext loc descr _)
  = mkLocMessage loc . addMessageContext descr


instance Error Message where
    noMsg  = empty
    strMsg = text
