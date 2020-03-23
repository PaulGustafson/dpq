-- | This module implements the command line dispatch function. 

module Dispatch (dispatch) where


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
import Printcircuits

import Nominal
import Graphics.EasyRender
import System.Exit
import System.Directory
import System.FilePath
import System.Environment
import System.Info
import System.IO
import System.Process

import qualified Data.MultiSet as S
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Except
import Text.PrettyPrint

-- | Perform top-level action on the command line input. The most complicated
-- piece of code is about loading a file, here we implement a very simple kind of
-- circularity checking for importation. We left implementing
-- a better module system as further work. 
dispatch :: Command -> Top Bool
dispatch Quit = return False
dispatch Help =
  do ioTop $ putStrLn usage
     return True
       where usage =
               "Commands:\n" ++
               "\n" ++
               "<expr>                  evaluate expression, use ';' to start a newline \n" ++
               ":l \"filename\"           read a dependently typed program from a file\n" ++
               ":t <expr>               show the classifier of an expression\n" ++
               ":a <fun-name>           show the annotation of a defined function\n" ++
               ":d <expr>               display a circuit in a previewer\n" ++
               ":e <expr>               display an existential circuit in a previewer\n" ++
               ":p <expr> \"filename\"    print a circuit to a file\n" ++
               ":r                      reload the most recent file, clear circuit state\n" ++
               ":s                      show the current top-level circuit\n" ++
               ":q                      exit interpreter\n" ++
               ":h                      show this list of commands\n" ++
               -- ":g <expr>               gate count" ++
               "\n" 


dispatch Reload =
  do f <- getFilename
     case f of
       Nothing -> throwError NoReloadError
       Just file -> dispatch (Load True file)


dispatch (ShowCirc) =
  do c <- getCirc
     let Morphism a gs b = c
         gs' = reverse gs
         c' = Morphism a gs' b
     liftIO $ putStrLn ("current circuit \n" ++ (show $ vcat $ map dispRaw gs') ++ "\n")
     let ws = getAllWires c'
         res = Wired $ abst ws (VCircuit c')
     tmpdir <- liftIO $ getTemporaryDirectory
     (pdffile, fd) <- liftIO $ openTempFile tmpdir "DPQ.pdf"
     ioTop $ printCirc_fd res fd
     liftIO $ hClose fd
     liftIO $ system_pdf_viewer 100 pdffile
     liftIO $ removeFile pdffile                     
     return True

dispatch (Type e) =
  do e' <- topResolve e
     (t', e'') <- topTypeInfer e'
     let fvs = getVars AllowEigen t'
     when (not $ S.null fvs) $ 
       throwError $ CompileErr $ TyAmbiguous Nothing t'
     liftIO $ putStrLn ("it has classifier \n" ++ (show $ disp t'))
     return True

dispatch (Eval e) =
  do e' <- topResolve e
     (t', e'') <- topTypeInfer e'
     if isKind t' then
         do liftIO $ putStrLn ("it has kind \n" ++ (show $ disp t'))
            n <- tcTop $ normalize e''
            liftIO $ putStrLn ("it normalizes to \n" ++ (show $ disp n))
            return True
       else do
         let fvs = getVars AllowEigen t'
         when (not $ S.null fvs) $ throwError $ CompileErr $ TyAmbiguous Nothing t'
         c <- getCirc
         (et, circ) <- tcTop $ erasure e'' >>= evaluate c
         putCirc circ
         liftIO $ putStrLn ("it has type \n" ++ (show $ disp t'))
         liftIO $ putStrLn ("it has value \n" ++ (show $ dispRaw et))
         return True

dispatch (Display e) =
  do e' <- topResolve e
     (t', et) <- topTypeInfer e'
     et <- tcTop $ erasure et
     case t' of
       A.Circ _ _ _ ->
         do res <- tcTop $ evaluation et
            tmpdir <- liftIO $ getTemporaryDirectory
            (pdffile, fd) <- liftIO $ openTempFile tmpdir "DPQ.pdf"
            ioTop $ printCirc_fd res fd
            liftIO $ hClose fd
            liftIO $ system_pdf_viewer 100 pdffile
            liftIO $ removeFile pdffile            
            return True
       ty -> 
         do liftIO $ print (text "not a circuit")
            return True

dispatch (Print e file) =
  do e' <- topResolve e
     (t', et') <- topTypeInfer e'
     et <- tcTop $ erasure et'
     case t' of
       A.Circ _ _ _ ->
         do res <- tcTop $ evaluation et
            (ioTop $ printCirc res file)
            return True
       A.Exists (Abst n (A.Circ _ _ _)) _ ->
         do res <- tcTop $ evaluation et
            case res of
              A.VPair n circ -> 
                do -- liftIO $ print (text "input size:" $$ disp n)
                   liftIO $ printCirc circ file
                   return True
       ty -> 
         do liftIO $ print (text "not a circuit")
            return True

dispatch (GateCount name e) =
  do e' <- topResolve e
     (t', et') <- topTypeInfer e'
     et <- tcTop $ erasure et'
     case t' of
       A.Circ _ _ _ ->
         do res <- tcTop $ evaluation et
            let n = gateCount name res
            case name of
              Nothing ->
                do liftIO $ print (text "total gate:" $$ text (show n))
                   return True
              Just g ->
                do liftIO $ print (text (g++":") $$ text (show n))  
                   return True
       A.Exists (Abst n (A.Circ _ _ _)) _ ->
         do res <- tcTop $ evaluation et
            case res of
              A.VPair m circ -> 
                do let n = gateCount name res
                   case name of
                     Nothing ->
                       do liftIO $ print (text "total gate:" $$ text (show n))
                          return True
                     Just g ->
                       do liftIO $ print (text (g++":") $$ text (show n))  
                          return True
       ty -> 
         do liftIO $ print (text "not a circuit")
            return True

dispatch (DisplayEx e) =
  do e' <- topResolve e
     (t', et) <- topTypeInfer e'
     et <- tcTop $ erasure et
     case t' of
       A.Exists (Abst n (A.Circ _ _ _)) _ ->
         do res <- tcTop $ evaluation et
            case res of
              A.VPair _ circ -> 
                do tmpdir <- liftIO $ getTemporaryDirectory
                   (pdffile, fd) <- liftIO $ openTempFile tmpdir "Quipper.pdf"
                   liftIO $ printCirc_fd circ fd
                   liftIO $ hClose fd
                   liftIO $ system_pdf_viewer 100 pdffile
                   liftIO $ removeFile pdffile            
                   return True
       ty -> 
         do liftIO $ print (text "not an existential circuit")
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
           DefinedFunction (Just (a, _, av)) ->
             do liftIO $ putStrLn ("it has annotation \n" ++ (show $ dispRaw a))
                -- liftIO $ putStrLn ("it has annotated value: \n" ++ (show $ dispRaw av))
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
     d1 <- addBuiltin (BuiltIn i) "Simple" A.Base
     d2 <- addBuiltin (BuiltIn (i+1)) "Parameter" A.Base
     d3 <- addBuiltin (BuiltIn (i+2)) "SimpParam" A.Base
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
     installMain
     ioTop $ hClose h
     when verbose $ liftIO $ putStrLn ("loaded: "++ takeFileName file)
     return True
       where
         installMain =
           do st <- getInterpreterState
              let cxt = context st
              case Map.lookup (Id "main") cxt of
                Nothing -> return ()
                Just info ->
                  let DefinedFunction (Just (_,v,_)) = identification info
                      t = classifier info
                  in putMain v t
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
                           decls' <- resolution decls
                           tcTop $ mapM process decls'
                           addImported file
                           ioTop $ hClose h
                           return ()



-- | Initialize instances of simple class for unit and tensor product.
initializeSimpleClass d = 
  do vpairs1 <- makeBuiltinClass d 1
     s <- topResolve (C.Base "Simple")
     i <- getCounter
     scope <- getScope
     putCounter (i+2)
     let inst1 = "instAt" ++ hashPos (BuiltIn i) ++ "Simple"
         inst2 = "instAt" ++ hashPos (BuiltIn (i+1)) ++ "Simple"
     (instSimp, scope') <- scopeTop $ addConst (BuiltIn i) inst1 Const scope
     (instSimp2, scope'') <- scopeTop $ addConst (BuiltIn (i+1)) inst2 Const scope'
     putScope scope''
     vpair <- tcTop $ elaborateInstance (BuiltIn i) instSimp (A.App s A.Unit) []
     let pt = freshNames ["a", "b"] $ \ [a, b] ->
           A.Forall (abst [a, b] $ A.Imply [A.App s (A.Var a), A.App s (A.Var b)]
                     (A.App s $ A.Tensor (A.Var a) (A.Var b))) A.Set
     tcTop $ elaborateInstance (BuiltIn (i+1)) instSimp2 pt []

-- | Initialize instances of SimpParam class for unit and tensor product.
initializeSimpParam d = 
  do vpairs1 <- makeBuiltinClass d 2
     s <- topResolve (C.Base "SimpParam")
     i <- getCounter
     scope <- getScope
     putCounter (i+2)
     let inst1 = "instAt" ++ hashPos (BuiltIn i) ++ "SimpParam"
         inst2 = "instAt" ++ hashPos (BuiltIn (i+1)) ++ "SimpParam"
     (instSimp, scope') <- scopeTop $ addConst (BuiltIn i) inst1 Const scope
     (instSimp2, scope'') <- scopeTop $ addConst (BuiltIn (i+1)) inst2 Const scope'
     putScope scope''
     tcTop $ elaborateInstance (BuiltIn i) instSimp (A.App (A.App s A.Unit) A.Unit) []
                           
     let pt = freshNames ["a", "b", "c", "d"] $ \ [a, b, c, d] ->
           A.Forall (abst [a, b, c, d] $ A.Imply [A.App (A.App s (A.Var a)) (A.Var c),
                                                  A.App (A.App s (A.Var b)) (A.Var d)]
                     (A.App (A.App s $ A.Tensor (A.Var a) (A.Var b)) (A.Tensor (A.Var c) (A.Var d)))) A.Set
     tcTop $ elaborateInstance (BuiltIn (i+1)) instSimp2 pt []

-- | Initialze instances of Parameter class for unit, bang type and tensor product.
initializeParameterClass d = 
  do vpairs1 <- makeBuiltinClass d 1
     s <- topResolve (C.Base "Parameter")
     i <- getCounter
     putCounter (i+4)
     scope <- getScope
     let inst1 = "instAt" ++ hashPos (BuiltIn i) ++ "Parameter"
         inst2 = "instAt" ++ hashPos (BuiltIn (i+1)) ++ "Parameter"
         inst3 = "instAt" ++ hashPos (BuiltIn (i+2)) ++ "Parameter"
         inst4 = "instAt" ++ hashPos (BuiltIn (i+3)) ++ "Parameter"
     (instP, scope') <- scopeTop $ addConst (BuiltIn i) inst1 Const scope
     (instP2, scope'') <- scopeTop $ addConst (BuiltIn (i+1)) inst2 Const scope'
     (instP3, scope''') <- scopeTop $ addConst (BuiltIn (i+2)) inst3 Const scope''
     putScope scope'''
     tcTop $ elaborateInstance (BuiltIn i) instP (A.App s A.Unit) []
     let pt = freshNames ["a", "b"] $ \ [a, b] ->
           A.Forall (abst [a, b] $ A.Imply [A.App s (A.Var a), A.App s (A.Var b)]
                     (A.App s $ A.Tensor (A.Var a) (A.Var b))) A.Set
     tcTop $ elaborateInstance (BuiltIn (i+1)) instP2 pt []
     let pt2 = freshNames ["a"] $ \ [a] ->
           A.Forall (abst [a] (A.App s $ A.Bang (A.Var a) identityMod)) A.Set
     tcTop $ elaborateInstance (BuiltIn (i+2)) instP3 pt2 []


-- | @'system_pdf_viewer' zoom pdffile@: Call a system-specific PDF
-- viewer on /pdffile/ file. The /zoom/ argument is out of 100 and may
-- or may not be ignored by the viewer.
system_pdf_viewer :: Double -> String -> IO ()
system_pdf_viewer zoom pdffile = do
  envList <- getEnvironment
  if (elem ("OS", "Windows_NT") envList)
    then do rawSystem "acroread.bat" [pdffile] `catchError` \ e -> handleErr
            return ()
    else if (os == "darwin")
         then do
           rawSystem "open" [pdffile]
           rawSystem "sleep" ["1"] -- required or the file may be deleted too soon
           return ()
         else -- try acroread first, if it fails, try xpdf.
           do rawSystem "acroread" ["/a", "zoom=100", pdffile]
                `catchError` \ e -> rawSystem "xpdf" [pdffile]
                `catchError` \ e -> handleErr
              return ()
  where handleErr =
          do print (text "we currently only support acroread and xpdf for display" $$
                    text "please use the :p command to print the circuit to a file")
             return $ ExitFailure 1     



