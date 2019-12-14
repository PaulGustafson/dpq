{-# LANGUAGE FlexibleInstances, FlexibleContexts, GeneralizedNewtypeDeriving #-}
module TCMonad where

import Utils
import Syntax
import TypeError
import Substitution

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

