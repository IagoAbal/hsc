
{-# LANGUAGE GADTs #-}

module H.Syntax.Pattern where


import H.Syntax.AST
import H.Syntax.Expr
  ( mkSkolemVar
  , mkApp, mkTyApp, splitApp
  , tcNilCon, tcConsCon )
import H.Syntax.IsTc
import H.Syntax.Phase
import H.Syntax.Type ( tau2sigma, mu_0 )

import Name
import Unique ( Uniq )


isVarPat :: Pat p -> Bool
isVarPat (VarPat _) = True
isVarPat _other     = False

mkNILPat :: IsTc p => Tau p -> Pat p
mkNILPat ty = ConPat tcNilCon (PostTc [ty]) []

mkCONSPat :: IsTc p => Tau p -> Pat p -> Pat p -> Pat p
mkCONSPat ty p1 p2 = ConPat tcConsCon (PostTc [ty]) [p1,p2]

mkInfixCONSPat :: IsTc p => Tau p -> Pat p -> Pat p -> Pat p
mkInfixCONSPat ty p1 p2 = InfixCONSPat (PostTc ty) p1 p2

-- | Converts a pattern to an expression.
pat2exp :: IsTc p => Pat p -> Exp p
pat2exp (LitPat lit) = Lit lit
pat2exp (VarPat x)   = Var x
pat2exp (InfixCONSPat (PostTc typ) p1 p2)
  = InfixApp (pat2exp p1) conE (pat2exp p2)
  where conE = mkTyApp (Op CONSOp) [typ]
pat2exp (ConPat con (PostTc typs) ps)
  = conE `mkApp` map pat2exp ps
  where conE = mkTyApp (Con con) typs
pat2exp (TuplePat ps tup_ty) = Tuple tup_ty $ map pat2exp ps
pat2exp (ListPat ps list_ty) = List list_ty $ map pat2exp ps
pat2exp (ParenPat p) = Paren $ pat2exp p
pat2exp (WildPat wild_var)
  = Var wild_var
pat2exp (AsPat _ p)  = pat2exp p
-- pat2exp (SigPat p ty) = pat2exp p
pat2exp _other = undefined -- impossible

-- *** Simple patterns

-- | SimplePat = VarPat | LitPat | ConPat | TuplePat
type SimplePat = Pat

simplifyPats :: [Pat Ti] -> ([SimplePat Ti],[(Var Ti,Exp Ti)])
simplifyPats pats = let (pats',pats_ss) = unzip $ map simplifyPat pats
                      in (pats',concat pats_ss)
                      
simplifyPat :: Pat Ti -> (SimplePat Ti,[(Var Ti,Exp Ti)])
simplifyPat p@(VarPat _) = (p,[])
simplifyPat p@(LitPat _) = (p,[])
simplifyPat (InfixCONSPat (PostTc typ) p1 p2)
  = (mkCONSPat typ p1' p2',bs)
  where ([p1',p2'],bs) = simplifyPats [p1,p2]
simplifyPat (ConPat con ptctyps ps) = (ConPat con ptctyps ps',bs)
  where (ps',bs) = simplifyPats ps
simplifyPat (TuplePat ps ptcty) = (TuplePat ps' ptcty,bs)
  where (ps',bs) = simplifyPats ps
simplifyPat (ListPat ps (PostTc list_ty)) =
    (foldr (mkCONSPat elem_ty) (mkNILPat elem_ty) ps',bs)
  where ListTy elem_ty = mu_0 list_ty
        (ps',bs) = simplifyPats ps
  -- NB: ParenPat is just convenient for pretty-printing
  -- when we have InfixCONSPat's
simplifyPat (ParenPat p) = (p',bs)
  where (p',bs) = simplifyPat p
simplifyPat (WildPat wild_var) = (VarPat wild_var,[])
  -- NB: `p' cannot depend on `v' nor vice-versa
simplifyPat (AsPat v p) = (p',(v,pat2exp p):bs)
  where (p',bs) = simplifyPat p
simplifyPat _other = undefined -- impossible


patBndrs :: Pat p -> [VAR p]
patBndrs (VarPat var) = [var]
patBndrs (LitPat _lit) = []
patBndrs (InfixCONSPat _ p1 p2) = patBndrs p1 ++ patBndrs p2
patBndrs (ConPat _con _ ps) = patsBndrs ps
patBndrs (TuplePat ps _) = patsBndrs ps
patBndrs (ListPat ps _) = patsBndrs ps
patBndrs (ParenPat p) = patBndrs p
patBndrs WildPatIn    = []
patBndrs (WildPat var)  = [var]
patBndrs (AsPat v p)  = v : patBndrs p
-- patBndrs (SigPat p _t) = patBndrs p

patsBndrs :: [Pat p] -> [VAR p]
patsBndrs = concatMap patBndrs


instWildPat :: Uniq -> Tau p -> Var p
instWildPat uniq tau
  = mkSkolemVar (mkSysName (mkOccName VarNS "x") uniq) (tau2sigma tau)

-- | Check if an arbitrary expression could be matched against some
-- given pattern. This is an undecidable problem and hence the purpose of
-- this function is to detect trivial errors: it is conservative
-- considering that an expression may match a pattern in case of doubt.
-- NB: It *requires* that the given expression and pattern have compatible types.
-- e.g. @Just 1 `matchableWith` Nothing == False@
-- e.g. @tail [x] `matchableWith (y::ys) == True@ because @tail@ is a function
matchableWith :: IsTc p => Exp p -> Pat p -> Bool
matchableWith _e            (VarPat _)    = True
matchableWith _e            (WildPat _)   = True
matchableWith (Lit lit)     (LitPat lit') = lit == lit'
  -- 'p' is not a 'VarPar' nor a 'LitPat' so matching is not possible
matchableWith (Lit _)       _p            = False
matchableWith (List _ es)   (ListPat ps _)
  | length es == length ps = and $ zipWith matchableWith es ps
  | otherwise              = False
  -- if types are compatible then @length es == length ps@
matchableWith (Tuple _ es)  (TuplePat ps _)
  = and $ zipWith matchableWith es ps
matchableWith e             p
  | Just (con,es) <- splitConApp e
  , ConPat con' _ ps <- p = if con == con'
                              then and $ zipWith matchableWith es ps
                              else False
    -- 'con' is a data constructor with no arguments, but 'InfixPat'
    -- implies a binary data constructor, here we detect that '[]'
    -- does not match _::_.
  | Just (_con,[]) <- splitConApp e
  , InfixCONSPat _ _ _ <- p = False
  where get_con (Con con)     = Just con
        get_con (TyApp e1 _)   = get_con e1
        get_con (Paren e1)     = get_con e1
        get_con (Coerc _ e1 _) = get_con e1
        get_con _other        = Nothing
        splitConApp e1 | Just con <- get_con f = Just (con,args)
                       | otherwise             = Nothing
          where (f,args) = splitApp e1
-- 'InfixApp'/'InfixPat' case is beign ignored for now because it is not
-- very interesting since only '::' can be used in a 'InfixPat'.
matchableWith (List _ [])   (InfixCONSPat _ _ _) = False
  -- since 'e' and 'p' are type-compatible and 'p' arguments are null,
  -- then we know 'p' is a '[]' pattern.
matchableWith (List _ (_:_)) (ConPat _ _ []) = False
matchableWith (List a (e:es)) (InfixCONSPat _ p ps)
  = matchableWith e p && matchableWith (List a es) ps
-- matchableWith e             (SigPat p _) = matchableWith e p
matchableWith (Coerc _ e _) p            = matchableWith e p
matchableWith (Paren e)     p            = matchableWith e p
matchableWith e             (ParenPat p) = matchableWith e p
  -- otherwise, be conversative and consider that 'e' matches 'p'
matchableWith _e            _p           = True

-- | Checks if two patterns are 'matchable', in the sense that their
-- "shapes" can be matched one against the other.
-- Some examples:
--   @matchablePats (_::_) (x::xs) == True@
--   @matchablePats [1,2,x] [1,2,_] == True@
--   @matchablePats (_::_) [] == False@
--   @matchablePats (1,b) (x,y) == True@
--   @matchablePats (a,b,c) (x,y) == False@
-- Note that this check does not detect any possible inconsistency,
-- for instance @matchablePats (x1::x2::xs) (y::(ys:{[]:[Int]})) == True@.
matchablePats :: IsTc p => Pat p -> Pat p -> Bool
matchablePats (VarPat _)  _           = True
matchablePats (WildPat _)    _           = True
matchablePats _           (VarPat _)  = True
matchablePats _           (WildPat _)     = True
matchablePats (LitPat l1) (LitPat l2) = l1 == l2
matchablePats (InfixCONSPat _ p1 p2) (InfixCONSPat _ p1' p2')
  = matchablePats p1 p1' && matchablePats p2 p2'
matchablePats (ConPat con _ ps) (ConPat con' _ ps')
  = con == con' && and (zipWith matchablePats ps ps')
matchablePats (TuplePat ps _) (TuplePat ps' _)
  = length ps == length ps' && and (zipWith matchablePats ps ps')
matchablePats (ListPat ps _) (ListPat ps' _)
  = length ps == length ps' && and (zipWith matchablePats ps ps')
matchablePats (ListPat (p:ps) ptcty) (InfixCONSPat _ p' q)
  = matchablePats p p' && matchablePats (ListPat ps ptcty) q
matchablePats (InfixCONSPat _ p q) (ListPat (p':ps') ptcty)
  = matchablePats p p' && matchablePats (ListPat ps' ptcty) q
matchablePats (ListPat [] _) (ConPat _ _ []) = True
matchablePats (ConPat _ _ []) (ListPat [] _) = True
matchablePats (ParenPat p) p'            = matchablePats p p'
matchablePats p            (ParenPat p') = matchablePats p p'
matchablePats (AsPat _ p)  p'            = matchablePats p p'
matchablePats p            (AsPat _ p')  = matchablePats p p'
-- matchablePats (SigPat p _) p'            = matchablePats p p'
-- matchablePats p            (SigPat p' _) = matchablePats p p'
matchablePats _p           _p'           = False