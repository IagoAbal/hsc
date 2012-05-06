
module H.Syntax.Expr where

import H.Syntax.AST ( Exp, Con, Prop, Sigma, Var )
import Name ( Name )


mkVarId :: Name -> Sigma p -> Var p

unitCon, trueCon, falseCon, nilCon, consCon :: Con p

zero :: Exp p

(.<.), (.<=.), (.>.), (.>=.) :: Exp p -> Exp p -> Prop p
