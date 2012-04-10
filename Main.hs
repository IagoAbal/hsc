{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE NamedFieldPuns #-}


module Main where

import H.Parser
import H.Renamer
import H.Typecheck
import H.Typecheck.TcM ( emptyTcEnv )
import H.Typecheck.Finalize
import H.Typecheck.TCC
import H.Desugar
import H.Monad ( runH, bindH_ )
import H.SrcContext
import H.SrcLoc
import Pretty
import Unique

import qualified Data.Binary as Binary
import System.Console.CmdArgs


data HC
  = Typecheck { srcFile :: FilePath }
    deriving (Typeable,Data)


typecheck_ = Typecheck{ srcFile = def &= argPos 0 &= typ "FILE" }
               &= help "Typechecker"

hc_ = modes [typecheck_ &= auto]
        &= program "hc"


executeCommand :: HC -> IO ()
executeCommand Typecheck{srcFile} = do
  f <- readFile srcFile
  let tc = bindH_ (parseH $ parseModuleWithMode (ParseMode "foo.h") f) () () $ \mod_pr ->
            bindH_ (rnModule mod_pr) emptyRnEnv () $ \mod_rn ->
            bindH_ (tcModule mod_rn) emptyTcEnv () $ \mod_tc ->
            bindH_ (finModule mod_tc) emptyTiEnv () $ \mod_ti ->
            bindH_ (coModule mod_ti) emptyCoEnv emptyCoST $ \modTCCs ->
            dsgModule mod_ti modTCCs
  (res,_) <- runH tc (SrcContext (SrcLoc "foo.h" 0 0) Pretty.empty False) newSupply () ()
  case res of
      Left err      -> putStrLn $ render err
      Right (m,_,_) -> Binary.encodeFile (srcFile ++ "c") m

main :: IO ()
main = executeCommand =<< cmdArgs hc_
