
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Core.Cert.SMT where

import Core.Syntax

import Pretty
import Unique ( Uniq )

import Data.Data
import qualified Data.Generics.Uniplate.Data as G
import Data.Hashable
import Data.List ( isPrefixOf, nub )
import qualified Data.Set as Set

import System.Process ( readProcess )

#include "bug.h"



data SMTProblem
  = SMTProblem {
    smtpTyParams :: [TyVar]
  , smtpDataTys  :: [Tau]
  , smtpFuns     :: [Exp]
  , smtpQVars    :: [Var]
  , smtpHypos    :: [Prop]
  , smtpProp     :: Prop
  }
  deriving Eq

instance Pretty SMTProblem where
  pretty (SMTProblem tps tys funs xs hypos prop)
    = text "SMTProblem" <+> braces (vcat
        [ text "ty-params =" <+> pp_list tps
        , text "data-tys =" <+> pp_list tys
        , text "funs =" <+> pp_list funs
        , text "xs =" <+> ppb_list xs
        , text "hypos =" <+> pp_list hypos
        , text "prop =" <+> pretty prop
        ])
    where pp_list ts = hsep (punctuate semi $ map pretty ts)
          ppb_list bs = hsep (punctuate semi $ map prettyBndr bs)


prop2problem :: Prop -> SMTProblem
prop2problem prop@(QP ForallQ xs body)
  = SMTProblem {
      smtpTyParams = Set.toList $ ftvOf prop
    , smtpDataTys = nub $
                      [ ty
                      | ty@(ListTy _) <- tausIn prop ++ tausIn fun_taus
                      ]
    , smtpFuns = nub $ [ fun
                       | fun@(TyApp (Par _) _) <- G.universe prop
                       ]
                       ++
                       [ fun
                       | fun@(Par f) <- G.universe prop
                       , isTau $ varType f
                       ]
    , smtpQVars = xs
    , smtpHypos = p_hypos
    , smtpProp = p_prop
  }
  where (p_hypos,p_prop) = unImp body
        fun_taus = [ instSigma (varType f) typs
                   | TyApp (Par f) typs <- G.universe prop
                   ]


instance Hashable Exp where
  hash e = hash [u | (u::Uniq) <- G.universeBi e]

instance Data c => Hashable (Type c) where
  hash ty = hash [u | (u::Uniq) <- G.universeBi ty]
 

yicesProblem :: SMTProblem -> Doc
yicesProblem (SMTProblem typs datatys funs params hypos prop)
  = vcat (map yicesTyParam typs)
  $$ vcat (map yicesData datatys)
  $$ vcat (map yicesFunParam funs)
  $$ vcat (map yicesParam params)
  $$ vcat (map yicesAssert hypos)
  $$ yicesAssert (not_ prop)
  $$ parens (text "check")

yicesTyVar :: TyVar -> Doc
yicesTyVar = pretty . tyVarName

yicesTyParam :: TyVar -> Doc
yicesTyParam a = parens $
    text "define-type" <+> y_a <+> (parens $ text "scalar" <+> y_a)
  where y_a = yicesTyVar a

yicesVar :: Var -> Doc
yicesVar = pretty

yicesData :: Tau -> Doc
yicesData (ListTy ty) = parens $
  text "define-type" <+> inst_id "list" <+> (parens $
    text "datatype" <+> inst_id "nil"
                    <+> (parens $ inst_id "cons"
                                  <+> inst_id "car" <> dcolon <> yicesTau ty
                                  <+> inst_id "cdr" <> dcolon <> inst_id "list"
                          )
     )
  where inst_id str = text str <> char '_' <> int (hash ty)

yicesFun :: Exp -> Doc
yicesFun (Par f) = yicesVar f
yicesFun fun@(TyApp (Par f) typs)
  = yicesVar f <> char '_' <> inst_id
  where inst_id = int $ hash fun
yicesFun _other = bug "yicesFun: not a supported function"

yicesFunParam :: Exp -> Doc
yicesFunParam fun@(Par f) = parens $
  text "define" <+> yicesFun fun <> dcolon <> yicesTau (varTau f)
yicesFunParam fun@(TyApp (Par f) typs) = parens $
  text "define" <+> yicesFun fun <> dcolon <> yicesTau fun_tau
  where fun_tau = instSigma (varType f) typs

yicesParam :: Var -> Doc
yicesParam x = parens $
  text "define" <+> yicesVar x <> dcolon <> yicesTau (varTau x)

yicesAssert :: Prop -> Doc
yicesAssert p = parens $ text "assert" <+> yicesExp p

yicesExp :: Exp -> Doc
yicesExp (Var x) = yicesVar x
yicesExp (Par f) = yicesVar f
yicesExp fun@(TyApp (Par _) typs) = yicesFun fun
yicesExp e | e == mkTrue = text "true"
yicesExp e | e == mkFalse = text "false"
yicesExp (isIntLit -> Just n) = integer n
yicesExp (TyApp (Con con) [ty]) | con == nilCon = yicesNil ty
yicesExp (PrefixApp op e) = parens $ yicesOp op <+> yicesExp e
yicesExp (InfixApp e1 op e2) = parens $
  yicesOp op <+> yicesExp e1 <+> yicesExp e2
yicesExp e@(App _ _) = parens $ yicesExp f <+> hsep (map yicesExp args)
  where (f,args) = splitApp e
yicesExp (Ite _ g e1 e2) = parens $
  text "ite" <+> yicesExp g <+> yicesExp e1 <+> yicesExp e2
--          | Tuple Tau [Exp] -- ^ tuple expression
--          | List Tau [Exp] -- ^ list expression
yicesExp (Paren e) = yicesExp e

yicesOp :: OpExp -> Doc
yicesOp (OpExp _ (BoolOp op))
  = case op of
        NotB  -> text "not"
        OrB   -> text "or"
        AndB  -> text "and"
        ImpB  -> text "=>"
        IffB  -> char '='
        EqB   -> char '='
        NeqB  -> text "/="
        LtB   -> char '<'
        LeB   -> text "<="
        GtB   -> char '>'
        GeB   -> text ">="
yicesOp (OpExp _ (IntOp op))
  = case op of
        NegI -> char '-'
        AddI -> char '+'
        SubI -> char '-'
        MulI -> char '*'
        DivI -> text "div"
        ModI -> text "mod"
yicesOp (OpExp [ty] CONSOp) = yicesCons ty

yicesListTy :: Tau -> Doc
yicesListTy ty = text "list" <> char '_' <> int (hash ty)

yicesNil :: Tau -> Doc
yicesNil ty = text "nil" <> char '_' <> int (hash ty)

yicesCons :: Tau -> Doc
yicesCons ty = text "cons" <> char '_' <> int (hash ty)

yicesTau :: Tau -> Doc
yicesTau (VarTy a) | skolemTyVar a = yicesTyVar a
yicesTau ty | ty == intTy = text "int"
yicesTau ty | ty == natTy = text "nat"
yicesTau ty | ty == boolTy = text "bool"
yicesTau (ListTy ty) = yicesListTy ty
yicesTau (PredTy (VarPat x) ty (Just prop)) = yicesSubtype x ty prop
yicesTau ty@(FunTy _ _) = parens $
  text "->" <+> hsep (map yicesDom ds) <+> yicesTau r
  where (ds,r) = unFunTy ty
yicesTau (TupleTy ds) = parens $
  text "tuple" <+> hsep (map yicesDom ds)
yicesTau other = bugDoc $ text "yicesTau: Not supported:" <+> pretty other

yicesSubtype :: Var -> Tau -> Prop -> Doc
yicesSubtype x ty prop = parens $
  text "subtype" <+> (parens $ yicesVar x <> dcolon <> yicesTau ty)
                 <+> yicesExp prop

yicesDom :: Dom -> Doc
yicesDom (Dom Nothing ty Nothing) = yicesTau ty
yicesDom (Dom (Just (VarPat x)) ty Nothing)
  = yicesVar x <> dcolon <> yicesTau ty
yicesDom (Dom (Just (VarPat x)) ty (Just prop))
  = yicesVar x <> dcolon <> yicesSubtype x ty prop


runYices :: Doc -> IO Bool
runYices spec = do
  out <- readProcess "yices" [] (render spec)
  return $ "unsat" `isPrefixOf` out

checkProp :: Prop -> IO ()
checkProp p = do
  res <- runYices $ yicesProblem $ prop2problem p
  if res
    then putStrLn "Q.E.D."
      -- We could use CEGAR to add new assertions based on the model
      -- in case we detect that the model is spurious.
    else putStrLn "Sorry, the property cannot be proven valid :-("
