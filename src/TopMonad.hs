{-# LANGUAGE FlexibleInstances, FlexibleContexts, GeneralizedNewtypeDeriving #-}
module TopMonad where


import Syntax as A
import ConcreteSyntax as C
import Parser
import TCMonad
import Typechecking
import Resolve
import TypeError
import Utils
import SyntacticOperations




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
  display a e = text ""

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

-- | perform an TCMonad without changing Top
tcTop :: TCMonad a -> Top a
tcTop m =
  do st <- getInterpreterState
     let cxt = context st
         inst = instCxt st
         (res, _) = runIdentity $ runTCMonadT cxt inst m
     case res of
       Left e -> throwError $ CompileErr e
       Right e -> return e

    
topTypeInfer :: A.Exp -> Top (A.Exp, A.Exp)
topTypeInfer e = tcTop $ typeInfer (isKind e) e 

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

