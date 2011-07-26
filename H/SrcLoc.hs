module H.SrcLoc where


import Text.PrettyPrint

-- | A position in the source
data SrcLoc = SrcLoc {
      srcFilename :: String
		, srcLine     :: Int
    , srcColumn   :: Int
		}
    deriving(Eq,Ord,Show)


ppSrcLoc :: SrcLoc -> Doc
ppSrcLoc (SrcLoc file line column)
  = hcat [text file, char ':', int line, char ':', int column]


ppLocated :: SrcLoc -> Doc -> Doc
ppLocated loc msg = ppSrcLoc loc <> char ':' <+> msg
