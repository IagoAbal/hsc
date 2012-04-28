
----------------------------------------------------------------------
-- |
-- Module      :  Bug
--
-- Maintainer  :  iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Utils for bug reporting.
-- See also bug.h
--
----------------------------------------------------------------------

module Bug
  ( _bug
  , _bugDoc
  , _impossible
  , _fromJust
  ) where

import Pretty ( Doc, errorDoc, text, ($$) )

type BugStuff = (String, Int, String, String)

_bug :: BugStuff -> String -> a
_bug bs s = _bugDoc bs (text s)

_bugDoc :: BugStuff -> Doc -> a
_bugDoc bs s = errorDoc $
   text ("bug at " ++ _bugLoc bs) $$ s

_bugLoc :: BugStuff -> String
_bugLoc (file, line, date, time) = file++":"++show line++" compiled "++time++" "++date

_impossible :: BugStuff -> a
_impossible bs = _bug bs $ "Impossible case at "++_bugLoc bs

_fromJust :: BugStuff -> Maybe a -> a
_fromJust bs mx =
  case mx of Nothing -> _bug bs $ "fromJust error at "++_bugLoc bs
             Just x  -> x
