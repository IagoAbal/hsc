
module Name where


import Unique

import Data.Function


-- * OccName

data OccName
  = OccName {
      occNameSpace :: !NameSpace
    , occString    :: !String
    }
    deriving(Eq,Ord)

data NameSpace = VarNS
               | ConNS
               | TyVarNS
               | TyConNS
               | GoalNS
    deriving(Eq, Ord)

mkOccName :: NameSpace -> String -> OccName
mkOccName = OccName


-- * Name

data NameSort = UserNm | SystemNm

data Name = Name { nameSort :: !NameSort
                 , nameOcc :: !OccName
                 , nameUniq :: !Uniq
                 }

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
