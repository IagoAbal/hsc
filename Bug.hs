
----------------------------------------------------------------------
-- |
-- Module      :  Bug
--
-- Maintainer  :  iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Utils for bug reporting, in the spirit of 'Darcs.Bug'.
-- See also bug.h
--
----------------------------------------------------------------------

module Bug
  ( _bug
  , _bugDoc
  , _impossible
  , _head
  , _tail
  , _fromJust
  ) where

import Pretty ( Doc, errorDoc, text, ($$), nest )

type BugStuff = (String, Int, String, String)

_bug :: BugStuff -> String -> a
_bug bs s = _bugDoc bs (text s)

_bugDoc :: BugStuff -> Doc -> a
_bugDoc bs s = errorDoc $
   text ("bug at " ++ _bugLoc bs ++ ":")
    $$ nest 2 s

_bugLoc :: BugStuff -> String
_bugLoc (file, line, date, time) = file++":"++show line++" compiled "++time++" "++date

_impossible :: BugStuff -> a
_impossible bs = _bug bs "the impossible happened"

_head :: BugStuff -> [a] -> a
_head bs l =
  case l of []    -> _bug bs "head error (empty list)"
            (x:_) -> x

_tail :: BugStuff -> [a] -> [a]
_tail bs l =
  case l of []     -> _bug bs $ "tail error (empty list)"
            (_:xs) -> xs

_fromJust :: BugStuff -> Maybe a -> a
_fromJust bs mx =
  case mx of Nothing -> _bug bs $ "fromJust error (Nothing)"
             Just x  -> x
