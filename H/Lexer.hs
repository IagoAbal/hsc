-- #hide
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Lexer
-- Copyright   :  (c) The GHC Team, 1997-2000
--                (c) Iago Abal, 2011
-- License     :  BSD-style (see the file libraries/base/LICENSE)
-- 
-- Maintainer  :  iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Lexer for H!.
--
-----------------------------------------------------------------------------

-- ToDo: Introduce different tokens for decimal, octal and hexadecimal (?)
-- ToDo: FloatTok should have three parts (integer part, fraction, exponent) (?)
-- ToDo: Use a lexical analyser generator (lx?)

module H.Lexer (Token(..), lexer) where

import H.ParseMonad

import Data.Char
  ( isAlpha, isLower, isUpper, toLower,
    isDigit, isHexDigit, isOctDigit, isSpace,
    ord, chr, digitToInt
  )
import qualified Data.Char (isSymbol)
import Data.Ratio

data Token
  = VarId String
  | ConId String
  | IntTok Integer

  -- Symbols
  | LeftParen
  | RightParen
  | SemiColon
  | LeftCurly
  | RightCurly
  | VRightCurly     -- a virtual close brace
  | LeftSquare
  | RightSquare
  | Comma
  | Underscore

  -- Reserved operators
  | DotDot
  | Colon
  | DoubleColon
  | Equals
  | Backslash
  | Bar
  | RightArrow
  | At
  | Minus

  -- Reserved Ids
  | KW_Case
  | KW_Data
  | KW_Else
  | KW_If
  | KW_In
  | KW_Let
  | KW_Module
  | KW_Of
  | KW_Then
  | KW_Type
  | KW_Where

  -- Special Ids
  -- nothing

  | EOF
  deriving (Eq,Show)

reserved_ops :: [(String,Token)]
reserved_ops = [
 ( "..", DotDot ),
 ( ":",  Colon ),
 ( "::", DoubleColon ),
 ( "=",  Equals ),
 ( "\\", Backslash ),
 ( "|",  Bar ),
 ( "->", RightArrow ),
 ( "@",  At )
 ]

special_varops :: [(String,Token)]
special_varops = [
 ( "-",  Minus )     --ToDo: shouldn't be here
 ]

reserved_ids :: [(String,Token)]
reserved_ids = [
 ( "_",       Underscore ),
 ( "case",    KW_Case ),
 ( "data",    KW_Data ),
 ( "else",    KW_Else ),
 ( "if",      KW_If ),
 ( "in",      KW_In ),
 ( "let",     KW_Let ),
 ( "module",  KW_Module ),
 ( "of",      KW_Of ),
 ( "then",    KW_Then ),
 ( "type",    KW_Type ),
 ( "where",   KW_Where )
 ]

special_varids :: [(String,Token)]
special_varids = [
 ]

isIdent, isSymbol :: Char -> Bool
isIdent  c = isAlpha c || isDigit c || c == '\'' || c == '_'
isSymbol c = c `elem` ":!#%&*./?@\\-" || (Data.Char.isSymbol c && not (c `elem` "(),;[]`{}_\"'"))

matchChar :: Char -> String -> Lex a ()
matchChar c msg = do
  s <- getInput
  if null s || head s /= c then fail msg else discard 1

-- The top-level lexer.
-- We need to know whether we are at the beginning of the line to decide
-- whether to insert layout tokens.

lexer :: (Token -> P a) -> P a
lexer = runL $ do
  bol <- checkBOL
  bol <- lexWhiteSpace bol
  startToken
  if bol then lexBOL else lexToken

lexWhiteSpace :: Bool -> Lex a Bool
lexWhiteSpace bol = do
  s <- getInput
  case s of
      '{':'-':_ -> do
          discard 2
          bol <- lexNestedComment bol
          lexWhiteSpace bol
      '-':'-':rest | all (== '-') (takeWhile isSymbol rest) -> do
          lexWhile (== '-')
          lexWhile (/= '\n')
          s' <- getInput
          case s' of
               [] -> fail "Unterminated end-of-line comment"
               _ -> do lexNewline
                       lexWhiteSpace True
      '\n':_ -> do lexNewline
                   lexWhiteSpace True
      '\t':_ -> do lexTab
                   lexWhiteSpace bol
      c:_ | isSpace c -> do discard 1
                            lexWhiteSpace bol
      _ -> return bol

lexNestedComment :: Bool -> Lex a Bool
lexNestedComment bol = do
  s <- getInput
  case s of
      '-':'}':_ -> discard 2 >> return bol
      '{':'-':_ -> do
          discard 2
          bol <- lexNestedComment bol -- rest of the subcomment
          lexNestedComment bol    -- rest of this comment
      '\t':_    -> lexTab >> lexNestedComment bol
      '\n':_    -> lexNewline >> lexNestedComment True
      _:_       -> discard 1 >> lexNestedComment bol
      []        -> fail "Unterminated nested comment"

-- When we are lexing the first token of a line, check whether we need to
-- insert virtual semicolons or close braces due to layout.

lexBOL :: Lex a Token
lexBOL = do
  pos <- getOffside
  case pos of
          -- Set col to 0, indicating that we're still at the
          -- beginning of the line, in case we need a semi-colon too.
          -- Also pop the context here, so that we don't insert
          -- another close brace before the parser can pop it.
      LT -> do setBOL
               popContextL "lexBOL"
               return VRightCurly
      EQ -> return SemiColon
      GT -> lexToken

lexToken :: Lex a Token
lexToken = do
    s <- getInput
    case s of
        [] -> return EOF
        '0':c:d:_ | toLower c == 'o' && isOctDigit d -> do
                       discard 2
                       n <- lexOctal
                       return (IntTok n)
                  | toLower c == 'x' && isHexDigit d -> do
                       discard 2
                       n <- lexHexadecimal
                       return (IntTok n)
        c:_ | isDigit c -> do n <- lexDecimal
                              return (IntTok n)
            | isUpper c -> lexConId
            | isLower c || c == '_' -> do
                 ident <- lexWhile isIdent
                 return $ case lookup ident (reserved_ids ++ special_varids) of
                               Just keyword -> keyword
                               Nothing -> VarId ident
            | isSymbol c -> do
                 sym <- lexWhile isSymbol
                 case lookup sym (reserved_ops ++ special_varops) of
                      Just t  -> return t
                      Nothing -> fail ("Unknown operator `" ++ sym ++ "'")
            | otherwise -> do
                 discard 1
                 case c of
                     -- First the special symbols
                     '(' ->  return LeftParen
                     ')' ->  return RightParen
                     ',' ->  return Comma
                     ';' ->  return SemiColon
                     '[' ->  return LeftSquare
                     ']' ->  return RightSquare
                     '{' -> do pushContextL NoLayout
                               return LeftCurly
                     '}' -> do popContextL "lexToken"
                               return RightCurly
                     _ ->    fail ("Illegal character \'" ++ show c ++ "\'\n")

lexConId :: Lex a Token
lexConId = do
  con <- lexWhile isIdent
  return (ConId con)


-- assumes at least one octal digit
lexOctal :: Lex a Integer
lexOctal = do
  ds <- lexWhile isOctDigit
  return (parseInteger 8 ds)

-- assumes at least one hexadecimal digit
lexHexadecimal :: Lex a Integer
lexHexadecimal = do
  ds <- lexWhile isHexDigit
  return (parseInteger 16 ds)

-- assumes at least one decimal digit
lexDecimal :: Lex a Integer
lexDecimal = do
  ds <- lexWhile isDigit
  return (parseInteger 10 ds)

-- Stolen from Hugs's Prelude
parseInteger :: Integer -> String -> Integer
parseInteger radix ds =
  foldl1 (\n d -> n * radix + d) (map (toInteger . digitToInt) ds)
