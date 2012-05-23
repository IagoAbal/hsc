{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE NamedFieldPuns #-}


module Main where

import qualified Core.Syntax as Core
-- import qualified Core.Syntax.Built as Core
import qualified Core.Cert.QuickCheck as Core
import qualified Core.Cert.SMT as Core

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
  | List { coreFile :: FilePath }
  | Check { coreFile :: FilePath, checkType :: CheckType, tccNum :: Int }
    deriving (Typeable,Data)

data CheckType = QuickCheck | SMTCheck
    deriving (Typeable,Data)

-- instance Show CheckType where
--   show QuickCheck = "quick"
--   show SMTCheck = "smt"

instance Default CheckType where
  def = QuickCheck

typecheck_, list_, check_, hc_ :: HC

typecheck_ = Typecheck{ srcFile = def &= argPos 0 &= typ "FILE" }
               &= help "Typechecker"

list_ = List{ coreFile = def &= argPos 0 &= typ "FILE" }
          &= help "List TCCs"

check_ = Check{ coreFile = def &= argPos 0 &= typ "FILE"
              , checkType = enum
                    [ QuickCheck &= explicit &= name "quick"
                                 &= help "randomized testing"
                    , SMTCheck   &= explicit &= name "smt"
                                 &= help "SMT verification"
                    ]
              , tccNum = def &= argPos 1 &= typ "TCC"
              }
          &= help "Check TCCs"

hc_ = modes [typecheck_ &= auto, list_, check_]
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
executeCommand List{coreFile} = do
  m <- Binary.decodeFile coreFile
  less $ render $ pretty $ Core.modTCCs m
executeCommand Check{coreFile,checkType,tccNum} = do
  m <- Binary.decodeFile coreFile
  case IMap.lookup tccNum $ Core.modTCCs m of
      Nothing  -> putStrLn "Error: TCC not found."
      Just tcc -> case checkType of
                      QuickCheck -> Core.checkProp tcc_PO
                      SMTCheck   -> putStrLn "Feature not supported yet."
        where tcc_PO = Core.tccGProp tcc

main :: IO ()
main = executeCommand =<< cmdArgs hc_


-- putStrLn $ render $ pretty $ Core.prop2problem tcc_PO
