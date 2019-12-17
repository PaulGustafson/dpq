module ProcessDecls where

import TCMonad
import Syntax
import SyntacticOperations
import Utils
import TypeError
import Typechecking
import Evaluation
import Erasure

import Nominal

import qualified Data.Map as Map
import Data.Map (Map)
import Data.List
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Except



-- data PState = PS {
--                   typingCxt :: Context,
--                   instanceCxt :: GlobalInstanceCxt,
--                   buildInClassId :: BuildInClass,
--                   valueEnv :: Map Id (Maybe Exp)
--                   }


-- type BuildInClass = [(String, Exp)]

-- -- | A monad for processing declarations
-- type ProcessDecl a = ExceptT TypeError (State PState) a


-- runP :: Context -> GlobalInstanceCxt -> BuildInClass -> Map Id (Maybe Exp) ->
--         ProcessDecl a -> (Either TypeError a, PState)
-- runP env inst bs vs m =
--   runIdentity $ runStateT (runExceptT m) (PS env inst bs vs)


process :: Decl -> TCMonad ()
process (Class pos d kd dict dictType mths) = 
  do let methodNames = map (\(_, s, _, _) -> s) mths
         tp = Info { classifier = erasePos kd,
                     identification = DictionaryType dict methodNames
                   }
     addNewId d tp
     checkVacuous pos dictType
     (_, dictTypeAnn) <- typeCheck True dictType Set 
     let fp = Info{ classifier = erasePos $ removeVacuousPi dictTypeAnn,
                    identification = DataConstr d
                 }
     addNewId dict fp              
     mapM_ (makeMethod dict methodNames) mths
       where makeMethod constr methodNames (pos, mname, mty, mty') =
               do let names = map getName methodNames
                      Just i = elemIndex (getName mname) names
                      mth = freshNames ("x":names) $ \ (x:mVars) ->
                        LamDict (abst [x] $ LetPat (Var x)
                                  (abst (PApp constr (map Right mVars))
                                   (Var $ mVars !! i)))
                      ty' = erasePos $ removeVacuousPi mty'
                      tyy = erasePos $ removeVacuousPi mty
                  checkVacuous pos ty'
                  (_, ty'') <- typeCheck True ty' Set
                  (_, tyy') <- typeCheck True tyy Set 
                  (_, a) <- typeCheck False (Pos pos mth) ty'' 
                  let fp = Info{ classifier = tyy',
                                 identification = DefinedMethod a
                              } 
                  addNewId mname fp

process (Def pos f' ty' def') =
  do checkVacuous pos ty'
     (_, ty) <- typeCheck True ty' Set 
     let ty1 = erasePos $ removeVacuousPi ty
     p <- isParam ty1
     when (not p) $
       throwError $ ErrPos pos (NotParam (Const f') ty')
     let info1 = Info { classifier = ty1,
                        identification = DefinedFunction Nothing}
     addNewId f' info1
     (ty2, ann) <- typeCheck True (Pos pos def') ty1 
     a <- erasure ann
     v <- eval a
     (ty2, annV) <- typeCheck True v ty1
     let info2 = Info { classifier = ty1,
                        identification = DefinedFunction (Just (ann, v, annV))}
     addNewId f' info2




