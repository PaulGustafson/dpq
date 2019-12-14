module ProcessDecls where

import TCMonad
import Syntax
import Utils
import TypeError

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Except



data PState = PS {
                  typingCxt :: Context,
                  instanceCxt :: GlobalInstanceCxt,
                  buildInClassId :: BuildInClass,
                  valueEnv :: Map Id (Maybe Exp)
                  }


type BuildInClass = [(String, Exp)]

-- | A monad for processing declarations
type ProcessDecl a = ExceptT TypeError (State PState) a


runP :: Context -> GlobalInstanceCxt -> BuildInClass -> Map Id (Maybe Exp) ->
        ProcessDecl a -> (Either TypeError a, PState)
runP env inst bs vs m =
  runIdentity $ runStateT (runExceptT m) (PS env inst bs vs)

{-
process :: Decl -> ProcessDecl ()
process (Class pos d kd dict dictType mths) = 
  do let methodNames = map (\(_, s, _, _) -> s) mths
         tp = Pkg {classifier = erasePos kd,
                   identification = DictionaryType dict methodNames
                   }
     insertNewConst d tp
     checkVacuous pos dictType
     annTy' <- kindChecking dictType Set True
     annTy <- defaultToElab $ betaNormalize annTy'
     let fp = Pkg{classifier = erasePos $ removeVacuousPi annTy,
                  identification = DataConstr d
                 }
     insertNewConst dict fp              
     -- trace ("this is dict:" ++ (show $ disp dict)) $ insertNewConst dict fp
     res <- mapM (makeMethod dict mNames) mths
     
     return ((dict, Nothing):res)
       where makeMethod constr mNames (pos, mname, mty, mty') =
               do let names = map getIdName mNames
                      Just i = elemIndex (getIdName mname) names
                      mth = with_fresh_namedS ("x":names)
                            $ \ (x:mVars) ->
                                LamDict (abst [x] $ LetPat (Var x)
                                        (abst (PApp constr (map (\ x -> Right (x, NoBind NonLinear)) mVars)
                                               
                                               )
                                         (Var $ mVars !! i))) -- [NonLinear]
                      ty' = erasePos $ removeVacuousPi mty'
                      tyy = erasePos $ removeVacuousPi mty
                  checkVacuous pos ty'
                  ty'' <- kindChecking ty' Set True
                  tyy' <- kindChecking tyy Set True
                  (_, a) <- typeChecking mname (Pos pos mth) ty'' False
                  -- a' <- defaultToElab $ erasure a
                  let fp = Pkg{classifier = tyy',
                               identification = DefinedMethod a
                              } 
                  insertNewConst mname fp
                  return ((mname, Just a))
-}


