module H.SrcLoc where


import H.Pretty


-- | A position in the source
data SrcLoc = SrcLoc {
      srcFilename :: String
		, srcLine     :: Int
    , srcColumn   :: Int
		}
    deriving(Eq,Ord,Show)


instance Pretty SrcLoc where
  pretty (SrcLoc file line column)
    = hcat [text file, char ':', int line, char ':', int column]

