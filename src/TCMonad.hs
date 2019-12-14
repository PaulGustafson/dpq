{-# LANGUAGE FlexibleInstances, FlexibleContexts, GeneralizedNewtypeDeriving #-}
module TCMonad where

import Utils
import Syntax
import TypeError
import Substitution
import SyntacticOperations
import Nominal

import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Except

import qualified Data.Map as Map
import Data.Map (Map)

data Info =
  Info { classifier :: Exp,
         identification :: Identification
       }

data Identification = DataConstr Id  -- ^ Data type id 
                    | DefinedGate Exp
                    | DefinedFunction Exp
                    | DefinedMethod Exp 
                    | DefinedInstFunction Exp 
                    | DataType DataClassifier [Id] (Maybe Exp)
                      -- ^ A data type, its classifier and its
                      -- constructors, if it is simple type, then its runtime
                      -- template function.
                    | DictionaryType Id [Id] -- ^ Dictionary constructor and its methods id
                    deriving (Show)

data DataClassifier =
  Param 
  | SemiParam -- ^ Semi-parameter data type, e.g., List a
  | Simple -- ^ Types defined by the 'object' keyword. e.g. Qubit 
  | SemiSimple -- ^ Types defined by the 'simple' keyword. e.g. Vec a n 
  | Unknown 
  deriving (Show, Eq)

data VarInfo =
  VarInfo{ varClassifier :: Exp,
           varIdentification :: VarIdentification
         } 

data VarIdentification = TermVar ZipCount (Maybe Exp)
                         -- ^ a term variable's count and let-definition if any.
                       | TypeVar Bool
                         -- ^ whether a type variable is a parameter variable


type Context = Map Id Info

data LContext = LContext {
  localCxt :: Map Variable VarInfo, -- ^ local variable info.
  globalCxt  :: Context  -- ^ global typing context.
  }

fromGlobal :: Context -> LContext
fromGlobal gl = LContext {localCxt = Map.empty, globalCxt = gl }


type GlobalInstanceCxt = [(Id, Exp)]


data InstanceContext = IC {
  localInstance :: [(Variable, Exp)],  -- ^ Local instance assumption.  
  globalInstance  :: GlobalInstanceCxt,  -- ^ Global instance identifiers and their types.
  goalInstance :: [(Variable, (Exp, Exp))]  -- ^ Current goal (constraint) variables that
                                             -- needed to be resolved. It has the format:
                                  -- (<variable>, (<type>, <original-term-for-error-info)).
  }

makeInstanceCxt :: GlobalInstanceCxt -> InstanceContext
makeInstanceCxt gl =
  IC {localInstance = [], globalInstance = gl, goalInstance = []}


data TypeState = TS {
                     lcontext :: LContext,
                     subst :: Subst, -- ^ Substitution generated during the type checking.
                     clock :: Int, -- ^ A counter 
                     instanceContext :: InstanceContext
                    }

-- | Initial type state from a global typing context and a
-- global type class instance context.
initTS :: Map Id Info -> GlobalInstanceCxt -> TypeState
initTS gl inst = TS (fromGlobal gl) Map.empty 0 (makeInstanceCxt inst)

-- * The type checking monad tranformer

newtype TCMonadT m a = TC{runTC :: ExceptT TypeError (StateT TypeState m) a}
  deriving (Functor, Monad, Applicative, MonadError TypeError, MonadState TypeState)

type TCMonad a = TCMonadT Identity a

runTCMonadT :: Context -> GlobalInstanceCxt -> 
                      TCMonadT m a -> m (Either TypeError a, TypeState)
runTCMonadT env inst m =
  runStateT (runExceptT $ runTC m) (initTS env inst) 

lookupId :: Id -> TCMonad Info
lookupId x =
  do ts <- get
     let gamma = lcontext ts
     case Map.lookup x (globalCxt gamma) of
       Nothing -> throwError (NoDef x)
       Just tup -> return tup

lookupVar :: Variable -> TCMonad (Exp, Maybe ZipCount)
lookupVar x =
  do ts <- get
     let gamma = lcontext ts
         lg = localCxt gamma
         s = subst ts
     case Map.lookup x lg of
       Nothing -> throwError $ UnBoundErr x 
       Just lp -> 
         do let a = substitute s $ varClassifier lp
                varid = varIdentification lp
            case varid of
              TermVar c _ -> return (a, Just c)
              _ -> return (a, Nothing)


isSemiSimple :: Id -> TCMonad Bool
isSemiSimple id =
  do tyinfo <- lookupId id
     case identification tyinfo of
       DataConstr dt ->
         do info <- lookupId dt
            case identification info of
              DataType SemiSimple _ _ -> return True
              _ -> return False
       _ -> return False

-- | Determine if a type expression is a parameter type. 
isParam :: Exp -> TCMonad Bool
isParam a | isKind a = return True
isParam (Unit) = return True
isParam (LBase id) = return False
isParam (Var x) =
   do ts <- get
      let gamma = lcontext ts
          lg = localCxt gamma
      case Map.lookup x lg of
        Nothing -> return False
        Just lti ->
          case varIdentification lti of
            TypeVar b -> return b
            _ -> return False

isParam (EigenVar x) =
   do ts <- get
      let gamma = lcontext ts
          lg = localCxt gamma
      case Map.lookup x lg of
        Nothing -> error "from isParam EigenVar"
        Just lti ->
          case varIdentification lti of
            TypeVar b -> return b
            _ -> return False

isParam (Base id) =
  do pac <- lookupId id
     case identification pac of
       DataType Param _ _ -> return True
       DataType _ _ _ -> return False


isParam t@(App x _) =
  case flatten t of
    Nothing -> return False
    Just (Right id, args) ->
      do tyinfo <- lookupId id
         case identification tyinfo of
           DataType Param _ _ -> return True
           DataType Simple _ _ -> return False
           DataType Unknown _ _ -> return False
           DataType _ _ _ -> helper tyinfo args
           DictionaryType _ _ -> return True
    _ -> error $ "isParam " ++ (show $ disp t)
  where helper tyinfo args =
          do let k = classifier tyinfo
                 (inds,h) = flattenArrows k
                 m = zip (map snd inds) args
             s <- mapM (\ (i, a) ->
                         if i == Set then isParam a
                         else if isKind i then return False else return True) m
             return $ and s

isParam t@(App' x _) =
  case flatten t of
    Nothing -> return False
    Just (Right id, args) ->
      do tyinfo <- lookupId id
         case identification tyinfo of
           DataType Param _ _ -> return True
           DataType Simple _ _ -> return False
           DataType Unknown _ _ -> return False
           DataType _ _ _ -> helper tyinfo args
           DictionaryType _ _ -> return True
    _ -> error $ "isParam " ++ (show $ disp t)
  where helper tyinfo args =
          do let k = classifier tyinfo
                 (inds,h) = flattenArrows k
                 m = zip (map snd inds) args
             s <- mapM (\ (i, a) ->
                         if i == Set then isParam a
                         else if isKind i then return False else return True) m
             return $ and s

isParam (Tensor t t') =
  do r1 <- isParam t     
     r2 <- isParam t'
     return $ r1 && r2

isParam (Arrow' t t') = return True
isParam (Pi' (Abst x t) ty) = return True
isParam (Imply xs t) = isParam t     
isParam (Bang q) = return True
isParam (Circ t1 t2) = return True
isParam (Pos _ e) = isParam e
isParam (Exists (Abst x t) ty) =
  do x <- isParam t
     y <- isParam ty
     return $ x && y
isParam a | otherwise = return False

-- | Increment the count of a variable by one.
updateCount :: Variable -> TCMonad ()
updateCount x = 
  do ts <- get
     let gamma = lcontext ts
         lty = localCxt gamma
     case Map.lookup x lty of
       Nothing -> error "from updateCount."
       Just lpkg ->
         case varIdentification lpkg of
           TypeVar b -> return ()
           TermVar c d ->
             do let lty' = Map.insert x (lpkg{varIdentification = TermVar (incr c) d}) lty
                    gamma' = gamma {localCxt = lty'}
                put ts{lcontext = gamma'}

     
shape a | isKind a = return a
shape Unit = return Unit
shape (LBase x) | getName x == "Qubit" = return Unit
shape a@(LBase x) | otherwise = return a
shape a@(Base _) = return a
shape a@(Const _) = return a
shape a@(Var _) = return a
shape a@(EigenVar _) = return a
shape a@(GoalVar _) = return a
shape a@(Bang _) = return a
shape a@(Lift _) = return a
shape a@(Circ _ _) = return a
shape a@(Force' m) = return a
shape (Force m) = shape m >>= \ x -> return (Force' x)
shape a@(App t1 t2) =
  case flatten a of
    Just (Right k, _) ->
      do p <- isParam a
         if p then return a
           else shapeApp t1 t2
    _ -> shapeApp t1 t2
  where shapeApp t1 t2 = 
          do t1' <- shape t1
             t2' <- shape t2
             return (App' t1' t2')         

shape a@(App' t1 t2) =
  case flatten a of
    Just (Right k, _) ->
      do p <- isParam a
         if p then return a
           else shapeApp t1 t2
    _ -> shapeApp t1 t2
  where shapeApp t1 t2 = 
          do t1' <- shape t1
             t2' <- shape t2
             return (App' t1' t2')         

shape a@(AppDep t1 t2) =
  case erasePos t1 of
    Box -> return $ AppDep' Box t2
    _ -> 
      do t1' <- shape t1
         t2' <- shape t2
         return (AppDep' t1' t2')         

shape a@(AppDep' _ _) = return a

shape (AppDict t1 t2) =
  do t1' <- shape t1
     return $ AppDict t1' t2

shape (AppType t1 t2) =
  do t1' <- shape t1
     return $ AppType t1' t2
     
shape (AppTm t1 t2) =
  do t1' <- shape t1
     return $ AppTm t1' t2
     
shape (Tensor t1 t2) = Tensor <$> shape t1 <*> shape t2

shape (Pair t1 t2) = Pair <$> shape t1 <*> shape t2

shape (Arrow t1 t2) = Arrow' <$> shape t1 <*> shape t2

shape (Imply bds h) = Imply <$> return bds <*> shape h


shape (Exists (Abst x t) t2) =
  do t' <- shape t
     t2' <- shape t2
     return $ Exists (abst x t') t2'
     
shape (Forall (Abst x t) t2) = 
  do t' <- shape t
     return $ Forall (abst x t') t2

shape a@(Arrow' _ _) = return a

shape (Pi (Abst x t) t2) =
  do t' <- shape t
     t2' <- shape t2
     return $ Pi' (abst x t') t2'
  
shape (Label x) = return Star

shape (Lam (Abst x t)) = 
  do t' <- shape t
     return $ Lam' (abst x t')

shape (LamDep (Abst x t)) =
  do t' <- shape t
     return $ LamDep' (abst x t')
     
shape (LamType (Abst x t)) =
  do t' <- shape t
     return $ LamType (abst x t')
     
shape (LamTm (Abst x t)) =
  do t' <- shape t
     return $ LamTm (abst x t')

shape (LamDict (Abst x t)) =
  do t' <- shape t
     return $ LamDict (abst x t')

shape RunCirc = return RunCirc
shape Box = return Box
shape UnBox = return UnBox
shape Revert = return Revert

shape (Case tm (B br)) =
  do tm' <- shape tm
     br' <- helper' br
     return $ Case tm' (B br')
  where helper' ps =
          mapM (\ b -> open b $
                       \ ys m ->
                       do m' <- shape m
                          return $ abst ys m')
          ps

shape a@(Wired _) = return a

shape (Let m bd) =
  do m' <- shape m 
     open bd $ \ y b ->
       do b' <- shape b
          return $ Let m' (abst y b') 

shape (LetPair m bd) =
  do m' <- shape m 
     open bd $ \ y b ->
       do b' <- shape b
          return $ LetPair m' (abst y b')
shape (LetEx m (Abst (x, y) b)) =
  do m' <- shape m
     b' <- shape b
     return $ LetEx m' (abst (x, y) b')

shape (LetPat m (Abst (PApp id vs) b)) =
  do m' <- shape m
     b' <- shape b
     return $ LetPat m' (abst (PApp id vs) b')
     
shape (Pos _ a) = shape a
shape a = error $ "from shape: " ++ (show $ disp a)
