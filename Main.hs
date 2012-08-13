{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}


module Main where

import qualified Core.Syntax as Core
-- import qualified Core.Syntax.Built as Core
import qualified Core.Cert.QuickCheck as CertQuick
import qualified Core.Cert.SMT as CertSMT

import H.Parser
import H.Renamer
import H.Typecheck ( tcModule )
import H.Typecheck.TcM ( emptyTcEnv )
import H.Typecheck.Finalize
import H.Typecheck.TCC ( coModule, emptyCoEnv, emptyCoST )
import H.Desugar
import H.Monad ( runH, bindH_ )
import H.SrcContext
import H.SrcLoc

import Pretty
import Unique

import Util.Less ( less )

import qualified Data.Binary as Binary
import qualified Data.IntMap as IMap
import System.Console.CmdArgs


data HC
  = Typecheck { srcFile :: FilePath }
  | List { coreFile :: FilePath, index :: Maybe Int }
  | Check { coreFile :: FilePath, checkType :: CheckType, index :: Maybe Int }
  | Show { coreFile :: FilePath }
    deriving (Typeable,Data)

data CheckType = QuickCheck | SMTCheck
    deriving (Typeable,Data)

-- instance Show CheckType where
--   show QuickCheck = "quick"
--   show SMTCheck = "smt"

instance Default CheckType where
  def = QuickCheck

typecheck_, list_, check_, show_, hc_ :: HC

typecheck_ = Typecheck{ srcFile = def &= argPos 0 &= typ "FILE" }
               &= help "Typechecker"

list_ = List{ coreFile = def &= argPos 0 &= typ "FILE"
            , index = def &= typ "RANGE"
            }
          &= help "List proof obligations"

check_ = Check{ coreFile = def &= argPos 0 &= typ "FILE"
              , checkType = enum
                    [ QuickCheck &= explicit &= name "quick"
                                 &= help "randomized testing"
                    , SMTCheck   &= explicit &= name "smt"
                                 &= help "SMT verification"
                    ]
              , index = def &= typ "RANGE"
              }
          &= help "Check TCCs"

show_ = Show{ coreFile = def &= argPos 0 &= typ "FILE" }
          &= help "Show Core"

hc_ = modes [typecheck_ &= auto, list_, check_, show_]
        &= program "hc"


executeCommand :: HC -> IO ()
executeCommand Typecheck{srcFile} = do
  f <- readFile srcFile
  let tc = bindH_ (parseH $ parseModuleWithMode (ParseMode srcFile) f) () () $ \mod_pr ->
            bindH_ (rnModule mod_pr) emptyRnEnv () $ \mod_rn ->
            bindH_ (tcModule mod_rn) emptyTcEnv () $ \mod_tc ->
            bindH_ (finModule mod_tc) emptyTiEnv () $ \mod_ti ->
            bindH_ (coModule mod_ti) emptyCoEnv emptyCoST $ \modTCCs ->
            dsgModule mod_ti modTCCs
  (res,_) <- runH tc (SrcContext (SrcLoc srcFile 0 0) Pretty.empty False) newSupply () ()
  case res of
      Left err      -> putStrLn $ render err
      Right (m,_,_) -> Binary.encodeFile (srcFile ++ "-core") m
executeCommand List{coreFile,index=Nothing} = do
  m <- Binary.decodeFile coreFile
  less $ render $ pretty $ Core.modPOs m
executeCommand List{coreFile,index=Just k} = do
  m <- Binary.decodeFile coreFile
  putStrLn $ render $ pretty $ Core.modPOs m IMap.! k
executeCommand Check{index=Nothing}
  = putStrLn "Nothing to do: you could give me a TCC to check."
executeCommand Check{coreFile,checkType,index=Just i} = do
  m <- Binary.decodeFile coreFile
  case IMap.lookup i $ Core.modPOs m of
      Nothing -> putStrLn "Error: TCC not found."
      Just po -> case checkType of
                     QuickCheck -> CertQuick.checkProp m po_formula
                     SMTCheck   -> CertSMT.checkProp po_formula
        where po_formula = Core.poFormula po
executeCommand Show{coreFile} = do
  m::Core.Module <- Binary.decodeFile coreFile
  less $ render $ pretty m


main :: IO ()
main = executeCommand =<< cmdArgs hc_
