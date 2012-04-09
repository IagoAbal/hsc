
module Core.Syntax.Built where

import Core.Syntax.AST
import Core.Syntax.FreeVars

import qualified Util.Set as Set

import qualified Data.Generics.Uniplate.Data as G
import qualified Data.Set as Set


val2bool :: Value -> Bool
val2bool t | t == mkTrue  = True
           | t == mkFalse = False
val2bool _other = undefined -- bug

bool2exp :: Bool -> Exp
bool2exp True = mkTrue
bool2exp False = mkFalse

cleanup :: Exp -> Exp
cleanup = G.transform f
  where f (QP _qt xs p)
          | Set.fromList xs `Set.disjointWith` fvExp p = p
        f (QP qt xs (QP qt1 ys p))
          | qt == qt1 = QP qt (xs ++ ys) p
        f (InfixApp e1 (OpExp [] (BoolOp OrB)) e2)
          | e1 == e2      = e1
          | e1 == mkTrue  = mkTrue
          | e2 == mkTrue  = mkTrue
          | e1 == mkFalse = e2
          | e2 == mkFalse = e1
        f (InfixApp e1 (OpExp [] (BoolOp AndB)) e2)
          | e1 == e2 = e1
          | e1 == mkTrue  = e2
          | e2 == mkTrue  = e1
          | e1 == mkFalse = mkFalse
          | e2 == mkFalse = mkFalse
        f (InfixApp e1 (OpExp [] (BoolOp ImpB)) e2)
          | e1 == e2 = mkTrue
          | e1 == mkTrue  = e2
          | e2 == mkTrue  = mkTrue
          | e1 == mkFalse = mkTrue
          | e2 == mkFalse = mkNot e1
        f (InfixApp e1 (OpExp [_] (BoolOp EqB)) e2)
          | e1 == e2 = mkTrue
        f t = t
