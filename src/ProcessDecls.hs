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
                                 identification = DefinedMethod a mth 
                              } 
                  addNewId mname fp

process (Instance pos f ty mths) =
  do checkVacuous pos ty
     let (env, ty') = removePrefixes False ty
         (bds, h) = flattenArrows ty'
         d = flatten h
     checkOverlap h `catchError` \ e -> throwError $ ErrPos pos e
     case d of
       Nothing -> throwError $ ErrPos pos $ TypeClassNotValid h
       Just (Right d', args) | getIdName d' == "Simple" ->
         throwError $ ErrPos pos $ ErrDoc $
         text "Simple class instance is not user-definable."
       Just (Right d', args) | getIdName d' == "SimpParam" ->
         throwError $ ErrPos pos $ ErrDoc $
         text "SimpParam class instance is not user-definable."
       Just (Right d', args) | getIdName d' == "Parameter" ->
         throwError $ ErrPos pos $ ErrDoc $
         text "Parameter class instance is not user-definable."         
       Just (Right d', args) ->
         elaborateInstance pos f ty mths


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
     a <- erasure $ unEigen ann
     v <- evaluation a
     (ty2, annV) <- typeCheck True v ty1
     let annV' = unEigen annV
     let info2 = Info { classifier = ty1,
                        identification = DefinedFunction (Just (ann, v, annV'))}
     addNewId f' info2




checkOverlap h =
  do es <- get
     let gs = glabalInstance $ instanceContext es
     mapM_ helper gs
  where helper (id, exp) =
          let (_, exp') = removePrefixes False exp
              (_, head) = flattenArrows exp'
              (r, _) = runMatch head h
          in if r then throwError $ InstanceOverlap h id exp
             else return ()

elaborateInstance pos f' ty mths =
  do (_, annTy) <- typeCheck True ty Set 
     let (env, ty') = removePrefixes False annTy
         vars = map (\ x -> case x of
                        (Just y, _) -> y
                    ) env
         sub0 = zip vars (map EigenVar vars)
         (bds0, h) = flattenArrows (apply sub0 ty')
         names = zipWith (\ i b -> "inst"++(show i)) [0 .. ] bds0
     case flatten h of
       Just (Right d', args) ->
         do dconst <- lookupId d'
            let DictionaryType c mm = identification dconst
                mm' = map (\ (_, x, _) -> x) mths
            when (mm /=  mm') $
             throwError $ ErrPos pos (MethodsErr mm mm')
            funPac <- lookupId c
            let constTy = classifier funPac
            let constTy' = instantiateWith constTy args
            let (bds, _) = flattenArrow constTy'
            freshNames names $ \ ns ->    
              do let instEnv = zip ns bds0
                 -- add the name of instance function and its type to the
                 -- global instance context, this enable recursive dictionary
                 -- construction.
                 addNewInst f' annTy
                 -- Type check and elaborate each method
                 ms' <- zipWithM (helper env instEnv) mths bds
                 
                 -- construct the annotated version of the instance function.
                 let def = foldl App (foldl AppType (Const const) args) ms'
                     def' = if null ns then rebind env def
                            else rebind env $ LamDict (abst ns def)
                                 -- (map (\ n -> NonLinear) ns)
                     a = unEigen def'
                     annTy' = erasePos annTy
                 -- a' <- defaultToElab $ erasure a
                 let fp = Pkg { classifier = annTy',
                                identification = DefinedInstFunction a 
                              }
                 insertNewConst f' fp
                 -- return ((f', Just a))
       _ -> throwError $ ErrPos pos $ TypeClassNotValid h                 
       where instantiateWith (Forall (Abst vs b') t) xs =
               let subs = zip vs xs
                   xs' = drop (length vs) xs
               in instantiateWith (apply subs b') xs'
             instantiateWith t xs = t
             helper env instEnv (p, _, m) t =
               let env' = map (\ x -> case x of
                                        Left a -> a
                                        Right a -> a
                                  ) env
               in typeCheckWithEnv env' instEnv (Pos p m) (erasePos t)
             rebind [] t = t
             rebind (Right (x, ty):res) t | isKind ty = LamType (abst [x] (rebind res t))
             rebind (Right (x, ty):res) t | otherwise = LamTm (abst [x] (rebind res t))

