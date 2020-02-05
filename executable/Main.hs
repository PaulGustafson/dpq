module Main where
import Dispatch
import Utils
import Syntax as A
import SyntacticOperations (gateCount)
import Printcircuits
import TopMonad
import ReadEvalPrint
import ConcreteSyntax

import Text.PrettyPrint
import Control.Exception
import Control.Monad.Except
import System.Exit
import System.Environment


main :: IO ()
main = 
  do args <- getArgs
     p <- getEnv "DPQ" `catches` handlers 
     case args of
       [filename, option, target] | option == "-p" ->
         runTop p $ catchTop error_handler $ (printToFile filename target)
       [filename, option] | option == "-m" ->
         runTop p $ catchTop error_handler (printMain filename)
       [filename, option] | option == "-g" ->
         runTop p $ catchTop error_handler (gateCountMain Nothing filename)
       [filename, option, name] | option == "-g" ->
         runTop p $ catchTop error_handler (gateCountMain (Just name) filename)         
       [filename] ->
         runTop p $ catchTop error_handler (load filename)
       _ ->
         do print $ text "unknown command option"
            print $ text cmdUsage
  where printMain fn = do
          dispatch (Load False fn)
          circ <- getMain
          case circ of
            Just (c, _) -> ioTop (print $ dispRaw c)
            Nothing ->
              throwError $ Mess DummyPos (text "cannot find the main function in:" <+> text fn)

        load fn = dispatch (Load False fn) >> return ()
          
        gateCountMain name file =
          do dispatch (Load False file)
             circ <- getMain
             case circ of
               Nothing ->
                 throwError $
                 Mess DummyPos (text "cannot find the main function in:" <+> text file)
               Just (circ', t) ->
                   case t of
                     A.Circ _ _ ->
                       do let n = gateCount name circ'
                          liftIO $ print (n :: Integer)
                     A.Exists (Abst m (A.Circ _ _)) _ ->
                       case circ' of
                         A.VPair _ res -> 
                           do let n = gateCount name res
                              liftIO $ print (n :: Integer)
                     ty -> liftIO $ print (text "main is not a circuit")
             
        printToFile file target = do
          dispatch (Load False file)
          circ <- getMain
          case circ of
            Nothing ->
              throwError $ Mess DummyPos (text "cannot find the main function in:" <+> text file)
            Just (circ', t) ->
                   case t of
                     A.Circ _ _ -> ioTop $ printCirc circ' target
                     A.Exists (Abst n (A.Circ _ _)) _ ->
                       case circ' of
                         A.VPair n res -> ioTop $ printCirc res target
                     ty -> liftIO $ print (text "main is not a circuit")
        error_handler e = 
          do top_display_error e
             return ()
            
        mesg = "please set the environment variable DPQ to the DPQ installation directory.\n"
        handlers = [Handler handle1]
        handle1 :: IOException -> IO String
        handle1 = \ ex  -> do putStrLn $ mesg ++ show ex
                              exitWith $ ExitFailure 1
        cmdUsage = "usage: dpq <dpq-file> [-options]\n\n" ++
                   "option: none             -- type check and evaluate given dpq file\n" ++
                   "option: -p <pdf-file>    -- print the main circuit to a pdf-file\n" ++
                   "option: -m               -- print the value of main function\n" ++
                   "option: -g [name]        -- print the gate count of main function\n"
