{-# LANGUAGE FlexibleInstances, FlexibleContexts, GeneralizedNewtypeDeriving #-}
module TopMonad where


import Syntax as A
import ConcreteSyntax as C
import Parser
import TCMonad
import TypeClass
import ProcessDecls
import Typechecking
import Resolve
import TypeError
import Utils
import SyntacticOperations


import Nominal

import Control.Monad.Except
import Control.Monad.Identity
import Control.Exception hiding (TypeError)
import Text.Parsec hiding (count)
import Text.PrettyPrint
import Control.Monad.State
import qualified Data.Map as Map
import Data.Map (Map)


data Error =
  NoReloadError  
  | IOError IOError  -- ^ Wrapper for IO error.
  | ScopeErr ScopeError -- ^ A wrapper for Scope error.
  | Mess Position Doc  -- ^ A wrapper for a message.
  | Cyclic Position [String] String -- ^ Cyclic importation error
  | ParseErr ParseError -- ^ A wrapper for parse error.
  | CompileErr TypeError -- ^ A wrapper for typing error.


instance Disp Error where
  display flag (IOError e) = text $ show e

  display flag NoReloadError = text "There is no file to reload"
  display flag (Mess p s) = display flag p $$ display flag s
  display flag (Cyclic p sources target) = display flag p $$
                                  text "cyclic importing detected" $$
                                  text "when importing:" <+> text target $$
                                  text "current importation chain:" $$
                                  (vcat $ map text sources)
  display flag (ParseErr e) = display flag e
  display flag (ScopeErr e) = display flag e
  display flag (CompileErr (PfErrWrapper a e)) =
    text "proof checking error:" $$
    display flag e $$
    text "when checking the following annotated term:" $$
    display flag a $$
    text "*************************" $$
    text "this is a bug, please send bug report. Thanks!"
    

  display flag (CompileErr e) = display flag e
    

-- | A toplevel monad
newtype Top a = T {runT :: ExceptT Error (StateT TopState IO) a }
              deriving (Monad, Applicative, Functor,
                        MonadState TopState, MonadError Error, MonadIO)

initTopState p = TopState {
  interpreterstate = emptyState p,
  filename = Nothing
  }


runTop :: String -> Top a -> IO a
runTop p body = 
  do (r, s') <- runStateT (runExceptT (runT body)) (initTopState p)
     case r of
       Right a -> return a
       Left e -> error ("from runTop: " ++ (show $ disp e)) 


-- | Interpretor's state.
data InterpreterState = InterpreterState {
  scope :: Scope,   -- ^ scope information.
  context :: Context,  -- ^ typing context.
  circ :: Morphism,  -- ^ top level incomplete circuit.
  mainExp :: Maybe (A.Exp, A.Exp),   -- ^ main value and its type.
  instCxt :: GlobalInstanceCxt, -- ^ type class instance context.
  parserState :: ParserState,   -- ^ infix operators table.
  parentFiles :: [String], -- ^ parent files, use to
                    -- prevent cyclic importing.
  importedFiles :: [String], -- ^ Imported files, prevent double importing.
  counter :: Int,
  path :: String
  }

data TopState = TopState {
  interpreterstate :: InterpreterState,
  filename :: Maybe String
  }


ioTop :: IO a -> Top a
ioTop x = T $ ExceptT $ lift (caught x)
  where caught :: IO a -> IO (Either Error a)
        caught x = catch (x >>= \y -> return (return y))
                   (\e -> return (Left (IOError e)))


getFilename :: Top (Maybe String)
getFilename = do
  s <- get
  return (filename s)

getCirc = do
  s <- getInterpreterState
  return (circ s)

getInterpreterState :: Top InterpreterState
getInterpreterState = do
  s <- get
  return (interpreterstate s)

getScope :: Top Scope
getScope = do
  s <- getInterpreterState
  return (scope s)

topResolve t =
  do scope <- getScope
     scopeTop $ resolve (toLScope scope) t

scopeTop :: Resolve a -> Top a
scopeTop x = case runResolve x of
                 Left e -> throwError (ScopeErr e)
                 Right a -> return a

-- | perform an TCMonad action, will update Top 
tcTop :: TCMonad a -> Top a
tcTop m =
  do st <- getInterpreterState
     let cxt = context st
         inst = instCxt st
         (res, s) = runIdentity $ runTCMonadT cxt inst m
     case res of
       Left e -> throwError $ CompileErr e
       Right e ->
         do let cxt' = globalCxt $ lcontext s
                inst' = globalInstance $ instanceContext s
            putCxt cxt'
            putInstCxt inst'
            return e

    
topTypeInfer :: A.Exp -> Top (A.Exp, A.Exp)
topTypeInfer def = tcTop $
  do (ty, tm) <- typeInfer (isKind def) def
     ty' <- updateWithSubst ty
     tm' <- updateWithSubst tm
     (ann1, rt) <- elimConstraint def tm' ty'
     let ann' = unEigen ann1
     rt' <- resolveGoals rt `catchError` \ e -> throwError $ withPosition def e
     ann'' <- resolveGoals ann' `catchError` \ e -> throwError $ withPosition def e
     return $ (rt', ann'')     
       where elimConstraint e a (A.Imply (b:bds) ty) = 
                 do ns <- newNames ["#outtergoalinst"]
                    freshNames ns $ \ [n] ->
                      do addGoalInst n b e
                         let a' = A.AppDict a (GoalVar n)
                         elimConstraint e a' (A.Imply bds ty)
             elimConstraint e a (A.Imply [] ty) = elimConstraint e a ty
             elimConstraint e a (A.Pos _ ty) = elimConstraint e a ty    
             elimConstraint e a t = return (a, t)


getCxt = do
  s <- getInterpreterState
  return (context s)

clearInterpreterState :: Top ()
clearInterpreterState =
  do p <- getPath
     putInterpreterState $ emptyState p

emptyState p = InterpreterState {
  scope = emptyScope,
  context = Map.empty,
  circ = Morphism A.Star [] A.Star,
  mainExp = Nothing,
  instCxt = [],
  parserState = initialParserState,
  parentFiles = [],
  importedFiles = [],
  counter = 0,
  path = p
  }

getPath :: Top String
getPath =
  do s <- get
     let intp = interpreterstate s
     return (path intp)

putInterpreterState :: InterpreterState -> Top ()
putInterpreterState is = do
  s <- get
  put $ s{interpreterstate = is}

getCounter :: Top Int
getCounter = do
  s <- getInterpreterState
  return (counter s)

addBuildin p x f =
  do scope <- getScope
     case lookupScope scope x of
       Just (_, oldp) -> error $ "internal error: from addBuildin"
       Nothing ->
         let 
             id = Id x
             exp = f id
             newMap = Map.insert x (exp, p) $ scopeMap scope
             scope' = scope{scopeMap = newMap}
         in putScope scope' >> return id

putScope :: Scope -> Top ()
putScope scope = do
  s <- getInterpreterState
  let s' = s { scope = scope }
  putInterpreterState s'

putCounter i = do
  s <- getInterpreterState
  let s' = s {counter = i}
  putInterpreterState s'


putFilename :: String -> Top ()
putFilename x = do
  s <- get
  let s' = s{filename = Just x }
  put s'

getPState = do
  s <- getInterpreterState
  return (parserState s)

putPState x = do
  s <- getInterpreterState
  let s' = s { parserState = x }
  putInterpreterState s'

-- | Update the typing context.
putCxt cxt = do
  s <- getInterpreterState
  let s' = s { context = cxt }
  putInterpreterState s'

-- | Update the instance context.
putInstCxt cxt = do
  s <- getInterpreterState
  let s' = s { instCxt = cxt }
  putInterpreterState s'


-- | Make a buildin class of the form c x1 ... xn, where c is the class name.
makeBuildinClass d c n | n > 0 =
  do i <- getCounter
     dict <- addBuildin (BuildIn (i+1)) (c++"Dict") A.Const
     putCounter (i+3)
     let names = map (\ i -> "x"++ show i) $ take n [0 .. ]
         dictType = freshNames names $
                    \ ns -> A.Forall (abst ns $ foldl A.App (A.Base d) (map A.Var ns)) A.Set
         kd = foldr (\ x y -> A.Arrow A.Set y) A.Set names
     tcTop $ process (A.Class (BuildIn (i+2)) d kd dict dictType [])

parserTop :: Either ParseError a -> Top a
parserTop (Left e) = throwError (ParseErr e)
parserTop (Right a) = return a

-- | Remember an imported file.
addImported :: String -> Top ()
addImported x = do
  s <- get
  let inS = interpreterstate s
      inS' = inS{importedFiles = x:(importedFiles inS)}
      s' = s{interpreterstate = inS'}
  put s'

-- | Remember an parent file.
addParentFile :: String -> Top ()
addParentFile x = do
  s <- get
  let inS = interpreterstate s
      inS' = inS{parentFiles = x:(parentFiles inS)}
      s' = s{interpreterstate = inS'}
  put s'

-- | Retrieve the parent files.
getParentFiles :: Top [String]
getParentFiles =
  do s <- get
     let intp = interpreterstate s
     return (parentFiles intp)

-- | Retrieve current imported files.
getCurrentImported :: Top [String]
getCurrentImported =
  do s <- get
     let intp = interpreterstate s
     return (importedFiles intp)

