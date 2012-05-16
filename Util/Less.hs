
module Util.Less where


import Control.Monad ( void )
-- import System.Exit ( ExitCode )
import System.IO ( hPutStr, hClose )
import System.Process



less :: String -> IO ()
less text = do
  (Just less_in, _, _, less_hdl) <- createProcess (proc "less" []){ std_in = CreatePipe }
  hPutStr less_in text
  hClose less_in
  void $ waitForProcess less_hdl
  
