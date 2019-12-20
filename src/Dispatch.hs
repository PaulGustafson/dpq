module Dispatch where


import ConcreteSyntax as C
import Syntax as A
import TopMonad
import TCMonad
import Utils
import Erasure
import Evaluation
import Normalize
import Parser
import SyntacticOperations
import TypeError
import Resolve
import ProcessDecls

import Nominal

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
           DefinedFunction (Just (a, _)) ->
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
     imports <- parserTop $ parseImports file str
     processImports imports
     pst <- getPState
     (decls, pst') <- parserTop $ parseModule file str pst
     putPState pst'
     decls' <- resolution decls
     tcTop $ mapM process decls'
     ioTop $ hClose h
     when verbose $ liftIO $ putStrLn ("loaded: "++ takeFileName file)
     return True
       where
         resolution [] = return []
         resolution (d:ds) =
           do sc <- getScope
              (d', sc') <- scopeTop $ resolveDecl sc d
              putScope sc'
              ds' <- resolution ds
              return (d':ds')
     
         -- | A helper function that is responsible for
         -- importing the files from the import declarations.
         processImports :: [C.Decl] -> Top ()
         processImports imps = mapM_ helper imps
           where helper (ImportGlobal p file) =
                   do fs <- getParentFiles
                      imps <- getCurrentImported
                      when ((file `elem` fs) && not (file `elem` imps)) $
                        throwError (Cyclic p fs file)
                      if file `elem` imps then
                        return ()
                        else 
                        do addParentFile file
                           path <- getPath
                           h <- ioTop $ openFile (path </> file) ReadMode
                           str <- ioTop $ hGetContents h
                           imports <- parserTop $ parseImports file str 
                           processImports imports
                           pst <- getPState
                           (decls, pst') <- parserTop $ parseModule file str pst
                           putPState pst'
                           --processDecls decls
                           decls' <- resolution decls
                           tcTop $ mapM process decls'
                           addImported file
                           ioTop $ hClose h
                           return ()




initializeSimpleClass d = 
  do vpairs1 <- makeBuildinClass d "Simple" 1
     s <- topResolve (C.Base "Simple")
     i <- getCounter
     scope <- getScope
     putCounter (i+2)
     let inst1 = "instAt" ++ hashPos (BuildIn i) ++ "Simple"
         inst2 = "instAt" ++ hashPos (BuildIn (i+1)) ++ "Simple"
     (instSimp, scope') <- scopeTop $ addConst (BuildIn i) inst1 Const scope
     (instSimp2, scope'') <- scopeTop $ addConst (BuildIn (i+1)) inst2 Const scope'
     putScope scope''
     vpair <- tcTop $ elaborateInstance (BuildIn i) instSimp (A.App s A.Unit) []
     let pt = freshNames ["a", "b"] $ \ [a, b] ->
           A.Forall (abst [a, b] $ A.Imply [A.App s (A.Var a), A.App s (A.Var b)]
                     (A.App s $ A.Tensor (A.Var a) (A.Var b))) A.Set
     tcTop $ elaborateInstance (BuildIn (i+1)) instSimp2 pt []


initializeSimpParam d = 
  do vpairs1 <- makeBuildinClass d "SimpParam" 2
     s <- topResolve (C.Base "SimpParam")
     i <- getCounter
     scope <- getScope
     putCounter (i+2)
     let inst1 = "instAt" ++ hashPos (BuildIn i) ++ "SimpParam"
         inst2 = "instAt" ++ hashPos (BuildIn (i+1)) ++ "SimpParam"
     (instSimp, scope') <- scopeTop $ addConst (BuildIn i) inst1 Const scope
     (instSimp2, scope'') <- scopeTop $ addConst (BuildIn (i+1)) inst2 Const scope'
     putScope scope''
     tcTop $ elaborateInstance (BuildIn i) instSimp (A.App (A.App s A.Unit) A.Unit) []
                           
     let pt = freshNames ["a", "b", "c", "d"] $ \ [a, b, c, d] ->
           A.Forall (abst [a, b, c, d] $ A.Imply [A.App (A.App s (A.Var a)) (A.Var c),
                                                  A.App (A.App s (A.Var b)) (A.Var d)]
                     (A.App (A.App s $ A.Tensor (A.Var a) (A.Var b)) (A.Tensor (A.Var c) (A.Var d)))) A.Set
     tcTop $ elaborateInstance (BuildIn (i+1)) instSimp2 pt []

-- | Initialze the 'Parameter' class and its three build-in instances,
-- i.e. unit, bang and tensor.
initializeParameterClass d = 
  do vpairs1 <- makeBuildinClass d "Parameter" 1
     s <- topResolve (C.Base "Parameter")
     i <- getCounter
     putCounter (i+4)
     scope <- getScope
     let inst1 = "instAt" ++ hashPos (BuildIn i) ++ "Parameter"
         inst2 = "instAt" ++ hashPos (BuildIn (i+1)) ++ "Parameter"
         inst3 = "instAt" ++ hashPos (BuildIn (i+2)) ++ "Parameter"
         inst4 = "instAt" ++ hashPos (BuildIn (i+3)) ++ "Parameter"
     (instP, scope') <- scopeTop $ addConst (BuildIn i) inst1 Const scope
     (instP2, scope'') <- scopeTop $ addConst (BuildIn (i+1)) inst2 Const scope'
     (instP3, scope''') <- scopeTop $ addConst (BuildIn (i+2)) inst3 Const scope''
     putScope scope'''
     tcTop $ elaborateInstance (BuildIn i) instP (A.App s A.Unit) []
     let pt = freshNames ["a", "b"] $ \ [a, b] ->
           A.Forall (abst [a, b] $ A.Imply [A.App s (A.Var a), A.App s (A.Var b)]
                     (A.App s $ A.Tensor (A.Var a) (A.Var b))) A.Set
     tcTop $ elaborateInstance (BuildIn (i+1)) instP2 pt []
     let pt2 = freshNames ["a"] $ \ [a] ->
           A.Forall (abst [a] (A.App s $ A.Bang (A.Var a))) A.Set
     tcTop $ elaborateInstance (BuildIn (i+2)) instP3 pt2 []
