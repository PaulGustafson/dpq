module Dispatch where


import ConcreteSyntax as C
import Syntax as A
import TopMonad
import TCMonad
import Utils
import Erasure
import Evaluation
import Normalize
import SyntacticOperations
import TypeError

import System.Directory
import System.FilePath
import System.Environment
import System.Info
import System.IO

import qualified Data.Set as S
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Except
import Text.PrettyPrint

dispatch :: Command -> Top Bool
dispatch Quit = return False
dispatch Help =
  do ioTop $ putStrLn usage
     return True
       where usage =
               "Commands:\n" ++
               "\n" ++
               "<expr>                  evaluate expression, use ';' to start a newline \n" ++
               ":l \"filename\"           read a dependentlty typed program from a file\n" ++
               ":t <expr>               show the classifier of an expression\n" ++
               ":a <fun-name>           show the annotation of a defined function\n" ++
               ":d <expr>               display a circuit in a previewer\n" ++
               ":e <expr>               display an existential circuit in a previewer\n" ++
               ":p <expr> \"filename\"    print a circuit to a file\n" ++
               ":r                      reload the most recent file, clear circuit state\n" ++
               ":s                      show the current top-level circuit\n" ++
               ":q                      exit interpreter\n" ++
               ":h                      show this list of commands\n" ++
               ":g <expr>               gate count" ++
               "\n" 


dispatch Reload =
  do f <- getFilename
     case f of
       Nothing -> throwError NoReloadError
       Just file -> dispatch (Load True file)


dispatch (ShowCirc) =
  do c <- getCirc
     let Morphism _ gs _ = c
     liftIO $ putStrLn ("current circuit \n" ++ (show $ vcat $ map dispRaw $ reverse gs) ++ "\n")
     return True

dispatch (Type e) =
  do e' <- topResolve e
     (t', e'') <- topTypeInfer e'
     let fvs = getVars AllowEigen t'
     when (not $ S.null fvs) $ throwError $ CompileErr $ TyAmbiguous Nothing t'
     liftIO $ putStrLn ("it has classifier \n" ++ (show $ disp t'))
     return True


-- TODO: need to handle when input is a type exp
dispatch (Eval e) =
  do e' <- topResolve e
     (t', e'') <- topTypeInfer e'
     -- (liftTCMonad $ proofCheck False e'' t') `catchError`
     --   (\ err -> throwError $ ProofCheckErr err (Id "<interactive>") e'' t')
     if isKind t' then
         do liftIO $ putStrLn ("it has kind \n" ++ (show $ disp t'))
            n <- tcTop $ normalize e''
            liftIO $ putStrLn ("it normalizes to \n" ++ (show $ disp n))
            return True
       else do
         let fvs = getVars AllowEigen t'
         when (not $ S.null fvs) $ throwError $ CompileErr $ TyAmbiguous Nothing t'
         et <- tcTop $ erasure e'' >>= evaluation 
         liftIO $ putStrLn ("it has type \n" ++ (show $ disp t'))
         -- res <- topEval et
         liftIO $ putStrLn ("it has value \n" ++ (show $ dispRaw et))
         return True


dispatch (Annotation e) =
  do cid <- topResolve e
     let (Const id) = cid
     env <- getCxt
     let dfs = env
     case Map.lookup id dfs of
       Nothing -> throwError $ Mess DummyPos (text "undefined constant:" <+> disp id )
         -- error "from dispatch annotation"
       Just p ->
         case identification p of
           DefinedFunction (Just (a, _, _)) ->
             do liftIO $ putStrLn ("it has annotation \n" ++ (show $ dispRaw a))
                return True
           DefinedMethod a _ ->
             do liftIO $ putStrLn ("it has annotation \n" ++ (show $ dispRaw a))
                return True                
           DefinedInstFunction a _ ->
             do liftIO $ putStrLn ("it has annotation \n" ++ (show $ dispRaw a))
                return True                
           _ ->   
             do liftIO $ putStrLn ("there is nothing to show \n")
                return True

{-
-- A load command will first initialize the Simple and Parameter class instances,
-- then proceed to load file. 
dispatch (Load verbose file) =
  do clearInterpreterState
     i <- getCounter
     d1 <- addBuildin (BuildIn i) "Simple" A.Base
     d2 <- addBuildin (BuildIn (i+1)) "Parameter" A.Base
     d3 <- addBuildin (BuildIn (i+2)) "SimpParam" A.Base
     putCounter (i+3)
     initializeSimpleClass d1
     initializeParameterClass d2
     initializeSimpParam d3
     putFilename file
     h <- ioTop $ openFile file ReadMode
     str <- ioTop $ hGetContents h
     imports <- parserToTop $ parseImports file str
     top_imports imports
     pst <- getPState
     (decls, pst') <- parserToTop $ parseModule file str pst
     putPState pst'
     processDecls decls
     ioTop $ hClose h
     when verbose $ liftIO $ putStrLn ("loaded: "++ takeFileName file)
     return True
       where
         -- | A helper function that is responsible for
         -- importing the files from the import declarations.
         top_imports :: [C.Decl] -> Top ()
         top_imports imps = mapM_ handleImport imps
           where handleImport (ImportGlobal p mod) =
                   do fs <- getParentFiles
                      imps <- getCurrentImported
                      let file = mod
                      when ((file `elem` fs) && not (file `elem` imps)) $
                        throwError (Cyclic p fs file)
                      if file `elem` imps then
                        return ()
                        else 
                        do addParentFile file
                           path <- getPath
                           h <- ioTop $ openFile (path </> file) ReadMode
                           str <- ioTop $ hGetContents h
                           imports <- parserToTop $ parseImports file str 
                           top_imports imports
                           pst <- getPState
                           (decls, pst') <- parserToTop $ parseModule file str pst
                           putPState pst'
                           processDecls decls
                           addImported file
                           ioTop $ hClose h
                           return ()



-}
