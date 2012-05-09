{-# LANGUAGE GADTs #-}


-- #hide
-----------------------------------------------------------------------------
-- |
-- Module      :  H.Parser.Utils
-- Copyright   :  (c) The GHC Team, 1997-2000
--                (c) Iago Abal, 2011
-- License     :  BSD-style (see the file libraries/base/LICENSE)
-- 
-- Maintainer  :  iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Utilities for the H! parser.
--
-----------------------------------------------------------------------------

module H.Parser.Utils
  where

import H.Syntax
import H.SrcLoc
import H.Parser.ParseMonad
import Pretty

import Name

import Control.Monad ( liftM )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.List ( nub )




mkFunTy :: Tau Pr -> Tau Pr -> Type c Pr
mkFunTy (PredTy pat a mbProp) b = dom @--> b
  where dom = Dom (Just pat) a mbProp
mkFunTy a b = a --> b

funWithSig :: (SrcLoc,NAME Pr,Sigma Pr) -> Bind Pr -> P (Bind Pr)
funWithSig (sigloc,sigfun,sigtype) (FunBind rec fun NoTypeSig None ms)
  | sigfun == fun = return $ FunBind rec fun sig None ms
  | otherwise     = fail ("Type signature for `" ++ prettyPrint sigfun ++ "' lacks an accompanying binding")
                        `atSrcLoc` sigloc
  where
      sig = TypeSig sigloc sigtype
funWithSig _tysig _other = undefined


-----------------------------------------------------------------------------
-- Group function bindings into equation groups

getMonoBind :: Bind Pr -> [Decl Pr] -> P (Bind Pr, [Decl Pr])
-- Suppose 	(b',ds') <- getMonoBind b ds
-- 	ds is a list of parsed bindings
--	b is a MonoBinds that has just been read off the front

-- Then b' is the result of grouping more equations from ds that
-- belong with b into a single MonoBinds, and ds' is the depleted
-- list of parsed bindings.
getMonoBind bind@(FunBind _ _ _ _ _) [] = return (bind,[])
  -- special case for functions of arity 0
  -- e.g. @x = 1@
  -- in this way @x = 1; x = 2@ will be reported as a duplicated
  -- definition instead of as a non-uniform definition.
getMonoBind bind@(FunBind rec fun sig None ms1@(Match _ [] _:_)) decls
  = return (bind,decls)
getMonoBind bind@(FunBind rec fun sig _ ms1@(Match _ ps _:_)) decls
  = mergeMatches ms1 decls
  where arity = length ps
        mergeMatches :: [Match Pr] -> [Decl Pr] -> P (Bind Pr, [Decl Pr])
        mergeMatches ms (ValDecl (FunBind _ fun' NoTypeSig None ms'@(Match (Just loc) ps' _:_)):ds)
          | fun' == fun = if length ps' /= arity
                            then fail ("arity mismatch for `" ++ prettyPrint fun ++ "'")
                                    `atSrcLoc` loc
                            else mergeMatches (ms ++ ms') ds
        mergeMatches ms ds = return (FunBind rec fun sig None ms,ds)
getMonoBind bind decls = return (bind,decls)



groupDeclsBinds :: [Decl Pr] -> P [Decl Pr]
groupDeclsBinds [] = return []
groupDeclsBinds (ValDecl bind@(FunBind _ _ _ _ _):decls)
  = do (bind',decls') <- getMonoBind bind decls
       liftM (ValDecl bind':) $ groupDeclsBinds decls'
groupDeclsBinds (decl:decls)
  = liftM (decl:) $ groupDeclsBinds decls


getParsedBinds :: [Decl Pr] -> [Bind Pr]
getParsedBinds []                = []
getParsedBinds (ValDecl bind:ds) = bind : getParsedBinds ds
getParsedBinds _other            = undefined


failDoc :: Doc -> P a
failDoc = fail . render

checkDupDecls :: [Decl Pr] -> P ()
checkDupDecls = go Map.empty
  where
    go :: Map OccName SrcLoc -> [Decl Pr] -> P ()
    go _booked [] = return ()
    go booked (TypeDecl loc name _ _:ds)
      = newDecl loc name booked >>= flip go ds
    go booked (DataDecl loc name _ constrs:ds)
      = foldl (>>=) (return booked) [ newDecl loc name
                                    | (loc,name) <- (loc,name):map getConName constrs]
          >>= flip go ds
    go booked (ValDecl (PatBind (Just loc) pat _):ds)
      = foldl (>>=) (return booked) [newDecl loc name | name <- patBndrs pat]
          >>= flip go ds
    go booked (ValDecl (FunBind _ name _ _ (Match (Just loc) _ _:_)):ds)
      = newDecl loc name booked >>= flip go ds
    go booked (GoalDecl loc _ name _ _:ds)
      = newDecl loc name booked >>= flip go ds
    getConName :: ConDecl Pr -> (SrcLoc,OccName)
    getConName (ConDeclIn loc name _) = (loc,name)
    newDecl loc name booked
      = case Map.lookup name booked of
            Nothing -> return $ Map.insert name loc booked
            Just loc1 ->
              failDoc (text "Multiple declarations of" <+> ppQuot name
                        $$ nest 2 (text "Declared at" <+> pretty loc1 <+> text "and" <+> pretty loc))
                `atSrcLoc` loc

