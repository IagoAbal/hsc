{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}

module Name where


import Unique

import Data.Binary ( Binary(..), getWord8, putWord8 )
import Data.Data ( Data, Typeable )
import Data.DeriveTH
import Data.Function


-- * OccName

data OccName
  = OccName {
      occNameSpace :: !NameSpace
    , occString    :: !String
    }
    deriving(Eq,Ord,Typeable,Data)

data NameSpace = VarNS
               | ConNS
               | TyVarNS
               | TyConNS
               | GoalNS
    deriving(Eq,Ord,Typeable,Data)

mkOccName :: NameSpace -> String -> OccName
mkOccName = OccName


-- * Name

data NameSort = UserNm | SystemNm
    deriving(Typeable,Data)

data Name = Name { nameSort :: !NameSort
                 , nameOcc :: !OccName
                 , nameUniq :: !Uniq
                 }
    deriving(Typeable,Data)

instance Eq Name where
  (==) = (==) `on` nameUniq

instance Ord Name where
  compare = compare `on` nameUniq

instance Uniquable Name where
  uniqOf = nameUniq

-- ** Constructors

mkUsrName :: OccName -> Uniq -> Name
mkUsrName = Name UserNm

mkSysName :: OccName -> Uniq -> Name
mkSysName = Name SystemNm

-- ** Named class

class Named a where
  nameOf :: a -> Name

occNameOf :: Named a => a -> OccName
occNameOf = nameOcc . nameOf

-- ** Fresh names

newName :: MonadUnique m => NameSpace -> String -> m Name
newName ns str = getUniq >>= return . mkSysName (mkOccName ns str)

newNameFrom :: MonadUnique m => Name -> m Name
newNameFrom nm = do uniq <- getUniq
                    return nm{nameUniq=uniq}



-- ! Binary instances generated through Template Haskell

$( derive makeBinary ''NameSpace )
$( derive makeBinary ''OccName )
$( derive makeBinary ''NameSort )
$( derive makeBinary ''Name )
