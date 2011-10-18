{-# OPTIONS_GHC -w #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  H.Pretty
-- Copyright   :  (c) The GHC Team, Noel Winstanley 1997-2000
--                (c) Iago Abal, 2011
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Pretty printer for H!.
--
-----------------------------------------------------------------------------

module H.Pretty where
--   ( -- * Pretty printing
--     Pretty,
--     ppStyleMode, ppWithMode, pp,
--     -- * Pretty-printing styles (from "Text.PrettyPrint.HughesPJ")
--     P.Style(..), P.style, P.Mode(..),
--     -- * Haskell formatting modes
--     PPMode(..), Indent, PPLayout(..), defaultMode
--   ) where


import Name

import Control.Monad
import Debug.Trace ( trace )
import qualified Text.PrettyPrint as P



infixl 5 $$$


-- * Pretty printing mode

-- | Pretty-printing parameters.
--
-- /Note:/ the 'onsideIndent' must be positive and less than all other indents.
data PPMode = PPMode {
        -- | indentation of the body of a
        -- @case@ expression
    caseIndent :: Indent,
        -- | indentation of the declarations in a
        -- @let@ expression
    letIndent :: Indent,
        -- | indentation of the declarations in a
        -- @where@ clause
    whereIndent :: Indent,
        -- | indentation added for continuation
        -- lines that would otherwise be offside
    onsideIndent :: Indent,
        -- | blank lines between statements?
    spacing :: Bool,
        -- | Pretty-printing style to use
    layout :: PPLayout
    }

type Indent = Int

-- | Varieties of layout we can use.
data PPLayout = PPOffsideRule -- ^ classical layout
              | PPSemiColon -- ^ classical layout made explicit
              | PPInLine  -- ^ inline decls, with newlines between them
              | PPNoLayout  -- ^ everything on a single line
    deriving Eq


-- | The default mode: pretty-print using the offside rule and sensible
-- defaults.
defaultMode :: PPMode
defaultMode = PPMode{
          caseIndent = 4,
          letIndent = 4,
          whereIndent = 6,
          onsideIndent = 2,
          spacing = True,
          layout = PPOffsideRule
          }


-- * DocM monad

-- | Pretty printing monad
newtype DocM s a = DocM (s -> a)

instance Functor (DocM s) where
   fmap f xs = do x <- xs; return (f x)

instance Monad (DocM s) where
  (>>=) = thenDocM
  (>>) = then_DocM
  return = retDocM

{-# INLINE thenDocM #-}
{-# INLINE then_DocM #-}
{-# INLINE retDocM #-}
{-# INLINE unDocM #-}
{-# INLINE getPPEnv #-}

thenDocM :: DocM s a -> (a -> DocM s b) -> DocM s b
thenDocM m k = DocM $ (\s -> case unDocM m $ s of a -> unDocM (k a) $ s)

then_DocM :: DocM s a -> DocM s b -> DocM s b
then_DocM m k = DocM $ (\s -> case unDocM m $ s of _ -> unDocM k $ s)

retDocM :: a -> DocM s a
retDocM a = DocM (\_s -> a)

unDocM :: DocM s a -> (s -> a)
unDocM (DocM f) = f

-- all this extra stuff, just for this one function.
getPPEnv :: DocM s s
getPPEnv = DocM id

-- So that pp code still looks the same
-- this means we lose some generality though


-- * Document type

-- | The document type produced by these pretty printers uses a 'PPMode'
-- environment.
type Doc = DocM PPMode P.Doc


-- * Pretty printing class

-- | Things that can be pretty-printed, including all the syntactic objects
-- in "Language.Haskell.Syntax".
class Pretty a where
  -- | Pretty-print something in isolation.
  pretty :: a -> Doc
  -- | Pretty-print something in a precedence context.
  prettyPrec :: Int -> a -> Doc
  pretty = prettyPrec 0
  prettyPrec _ = pretty

class PrettyBndr b where
  prettyBndr :: b -> Doc

-- Pretty printing of names

instance Pretty OccName where
  pretty = text . occString

instance PrettyBndr OccName where
  prettyBndr = pretty

instance Pretty Name where
  pretty (Name _ occ@(OccName ns _) uniq)
    = case ns of
          -- The 'OccName' for constructors is ensured to be unique
          ConNS   -> pretty occ
          TyConNS -> pretty occ
          -- For regular variables we need to print the 'Uniq'.
          _other  -> pretty occ <> char '_' <> int uniq

instance PrettyBndr Name where
  prettyBndr = pretty

-- * Pretty printing combinators

-- ** Literals

text, ptext :: String -> Doc
text = return . P.text
ptext = return . P.text

char :: Char -> Doc
char = return . P.char

int :: Int -> Doc
int = return . P.int

integer :: Integer -> Doc
integer = return . P.integer

float :: Float -> Doc
float = return . P.float

double :: Double -> Doc
double = return . P.double

rational :: Rational -> Doc
rational = return . P.rational

bool :: Bool -> Doc
bool True = text "True"
bool False = text "False"

-- ** Simple combining forms

parens, brackets, braces,quotes,doubleQuotes :: Doc -> Doc
parens d = d >>= return . P.parens
brackets d = d >>= return . P.brackets
braces d = d >>= return . P.braces
quotes d = d >>= return . P.quotes
doubleQuotes d = d >>= return . P.doubleQuotes

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

-- ** Constants

dot,semi,comma,colon,space,equals :: Doc
dot  = char '.'
semi = return P.semi
comma = return P.comma
colon = return P.colon
space = return P.space
equals = return P.equals

lparen,rparen,lbrack,rbrack,lbrace,rbrace :: Doc
lparen = return  P.lparen
rparen = return  P.rparen
lbrack = return  P.lbrack
rbrack = return  P.rbrack
lbrace = return  P.lbrace
rbrace = return  P.rbrace

-- Combinators

empty :: Doc
empty = return P.empty

nest :: Int -> Doc -> Doc
nest i m = m >>= return . P.nest i

(<>),(<+>),($$),($+$) :: Doc -> Doc -> Doc
(<>) = liftM2 (P.<>)
(<+>) = liftM2 (P.<+>)
($$) = liftM2 (P.$$)
($+$) = liftM2 (P.$+$)

hcat,hsep,vcat,sep,cat,fsep,fcat :: [Doc] -> Doc
hcat dl = sequence dl >>= return . P.hcat
hsep dl = sequence dl >>= return . P.hsep
vcat dl = sequence dl >>= return . P.vcat
sep dl = sequence dl >>= return . P.sep
cat dl = sequence dl >>= return . P.cat
fsep dl = sequence dl >>= return . P.fsep
fcat dl = sequence dl >>= return . P.fcat

-- Some More

hang :: Doc -> Int -> Doc -> Doc
hang dM i rM = do d <- dM; r <- rM; return $ P.hang d i r

-- Yuk, had to cut-n-paste this one from Pretty.hs
punctuate :: Doc -> [Doc] -> [Doc]
punctuate _ []      = []
punctuate p (d1:ds) = go d1 ds
  where go d []     = [d]
        go d (e:es) = (d <> p) : go e es


-- * Utils

ppMaybe :: (a -> Doc) -> Maybe a -> Doc
ppMaybe _pp Nothing  = empty
ppMaybe  pp (Just a) = pp a

ppQuot :: Pretty a => a -> Doc
ppQuot x = char '`' <> pretty x <> char '\''

parenList :: [Doc] -> Doc
parenList = parens . myFsepSimple . punctuate comma

braceList :: [Doc] -> Doc
braceList = braces . myFsepSimple . punctuate comma

bracketList :: [Doc] -> Doc
bracketList = brackets . myFsepSimple

-- Wrap in braces and semicolons, with an extra space at the start in
-- case the first doc begins with "-", which would be scanned as {-
flatBlock :: [Doc] -> Doc
flatBlock = braces . (space <>) . hsep . punctuate semi

-- Same, but put each thing on a separate line
prettyBlock :: [Doc] -> Doc
prettyBlock = braces . (space <>) . vcat . punctuate semi

-- Monadic PP Combinators
-- these examine the env

blankline :: Doc -> Doc
blankline dl = do e <- getPPEnv
                  if spacing e && layout e /= PPNoLayout
                     then space $$ dl
                     else dl

topLevel :: Doc -> [Doc] -> Doc
topLevel header dl = do
  e <- fmap layout getPPEnv
  case e of
      PPOffsideRule -> header $$ vcat dl
      PPSemiColon   -> header $$ prettyBlock dl
      PPInLine      -> header $$ prettyBlock dl
      PPNoLayout    -> header <+> flatBlock dl

ppBody :: (PPMode -> Int) -> [Doc] -> Doc
ppBody f dl = do
  e <- fmap layout getPPEnv
  i <- fmap f getPPEnv
  case e of
      PPOffsideRule -> nest i . vcat $ dl
      PPSemiColon   -> nest i . prettyBlock $ dl
      _             -> flatBlock dl

ppBindings :: [Doc] -> Doc
ppBindings dl = do
  e <- fmap layout getPPEnv
  case e of
      PPOffsideRule -> vcat dl
      PPSemiColon   -> vcat . punctuate semi $ dl
      _             -> hsep . punctuate semi $ dl

($$$) :: Doc -> Doc -> Doc
a $$$ b = layoutChoice (a $$) (a <+>) b

mySep :: [Doc] -> Doc
mySep = layoutChoice mySep' hsep
  where
  -- ensure paragraph fills with indentation.
  mySep' [x]    = x
  mySep' (x:xs) = x <+> fsep xs
  mySep' []     = error "Internal error: mySep"

myVcat :: [Doc] -> Doc
myVcat = layoutChoice vcat hsep

myFsepSimple :: [Doc] -> Doc
myFsepSimple = layoutChoice fsep hsep

-- same, except that continuation lines are indented,
-- which is necessary to avoid triggering the offside rule.
myFsep :: [Doc] -> Doc
myFsep = layoutChoice fsep' hsep
  where fsep' [] = empty
        fsep' (d:ds) = do
          e <- getPPEnv
          let n = onsideIndent e
          nest n (fsep (nest (-n) d:ds))

layoutChoice :: (a -> Doc) -> (a -> Doc) -> a -> Doc
layoutChoice a b dl = do
  e <- getPPEnv
  if layout e == PPOffsideRule || layout e == PPSemiColon
    then a dl
    else b dl


-- * Rendering documents

-- | render the document with a given style and mode.
renderStyleMode :: P.Style -> PPMode -> Doc -> String
renderStyleMode ppStyle ppMode d = P.renderStyle ppStyle . unDocM d $ ppMode

-- | render the document with a given mode.
renderWithMode :: PPMode -> Doc -> String
renderWithMode = renderStyleMode P.style

-- | render the document with 'defaultMode'.
render :: Doc -> String
render = renderWithMode defaultMode

-- | pretty-print with a given style and mode.
prettyPrintStyleMode :: Pretty a => P.Style -> PPMode -> a -> String
prettyPrintStyleMode ppStyle ppMode = renderStyleMode ppStyle ppMode . pretty

-- | pretty-print with the default style and a given mode.
prettyPrintWithMode :: Pretty a => PPMode -> a -> String
prettyPrintWithMode = prettyPrintStyleMode P.style

-- | pretty-print with the default style and 'defaultMode'.
prettyPrint :: Pretty a => a -> String
prettyPrint = prettyPrintWithMode defaultMode

fullRenderWithMode :: PPMode -> P.Mode -> Int -> Float ->
          (P.TextDetails -> a -> a) -> a -> Doc -> a
fullRenderWithMode ppMode m i f fn e mD =
       P.fullRender m i f fn e $ (unDocM mD) ppMode

fullRender :: P.Mode -> Int -> Float -> (P.TextDetails -> a -> a)
        -> a -> Doc -> a
fullRender = fullRenderWithMode defaultMode


-- * Tracing

traceDoc :: Doc -> a -> a
traceDoc = trace . render
