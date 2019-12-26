{-#LANGUAGE StandaloneDeriving #-}
import Dispatch
import TopMonad
import ReadEvalPrint
import ConcreteSyntax

import Control.Exception hiding (TypeError)
import System.FilePath
import System.Environment
import System.Exit


main :: IO ()
main = do
  p <- getEnv "DPQ" `catches` handlers 
  runTop p $
    catchTop error_handler $ do
       p <- getPath
       dispatch (Load True $ p </> "test/Qft.dpq")
       dispatch (Load True $ p </> "test/AdderN.dpq")
       -- dispatch (Load True $ p </> "test/Grover.dpq")              
       -- dispatch (Load True $ p </> "test/Controls.dpq")
       -- dispatch (Load True $ p </> "test/Exists.dpq")
       -- dispatch (Load True $ p </> "test/QftAdder.dpq")
       -- dispatch (Load True $ p </> "test/Qft.dpq")
       -- dispatch (Load True $ p </> "test/Tele.dpq")
       -- dispatch (Load True $ p </> "test/BWT.dpq")
       -- dispatch (Load True $ p </> "test/BWT2.dpq")
       -- dispatch (Load True $ p </> "test/March14.dpq")
       -- dispatch (Load True $ p </> "hex/Hex.dpq")
       -- dispatch (Load True $ p </> "hex/Hex2.dpq")
       -- dispatch (Load True $ p </> "hex/Hex3.dpq")
       -- dispatch (Load True $ p </> "hex/Hex4.dpq")
       return () 
   where error_handler e = 
          do top_display_error e
             return ()
        
         mesg = "please set the enviornment variable DPQ to the DPQ installation directory.\n"
         handlers = [Handler handle1]
         handle1 :: IOException -> IO String
         handle1 = (\ ex  -> do {putStrLn $ mesg ++ show ex; exitWith (ExitFailure 1)})
