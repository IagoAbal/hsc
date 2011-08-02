{-# LANGUAGE TypeSynonymInstances #-}

module H.Message where

import H.Pretty
import H.SrcLoc

import Control.Monad.Reader.Class
import Control.Monad.Error.Class( Error(..) )


-- * Message

type Message = Doc
type MsgContext = Doc


atSrcLoc :: Message -> SrcLoc -> Message
msg `atSrcLoc` loc = pretty loc <> char ':'
                      $$ nest 2 msg

inContext :: Message -> MsgContext -> Message
msg `inContext` ctx = msg $$ ctx

instance Error Message where
    noMsg  = empty
    strMsg = text
