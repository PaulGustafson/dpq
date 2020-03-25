{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- | This module processes Proto-Quipper-D declarations. For object and simple type declarations,
-- the type checker will generate instances for 'Simple', 'Parameter' and 'SimpParam' classes.
-- Each simple type
-- declaration also gives rise to a function that turns the simple type into a simple term.
-- We support two kinds of gate declarations, an ordinary gate declaration and a generic
-- control gate declaration. We support Haskell 98 style data type declaration with type class
-- constraint. Moreover, we support existential dependent data type in this
-- format. All top level functions must be of parameter types. Functions can be defined 
-- by first giving its type annotation, or one can just annotate the types
-- for its arguments (in that case dependent pattern matching is not supported). 


module ProcessDecls (process, elaborateInstance) where

import TCMonad
import Syntax
import SyntacticOperations
import Utils
import TypeError
import ModeResolve
import Typechecking
import Proofchecking
import Evaluation hiding (genNames)
import Erasure
import Substitution
import TypeClass
import Simplecheck
import Nominal hiding ((.))

import qualified Data.Map as Map
import Data.Map (Map)
import Data.List
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Except
import Text.PrettyPrint
import Debug.Trace
import qualified Data.MultiSet as S

-- | Process a top-level declaration, modifying the state in the TCMonad. 
process :: Decl -> TCMonad ()
process (Class pos d kd dict dictType mths) = 
  do let methodNames = map (\(_, s, _) -> s) mths
         tp = Info { classifier = erasePos kd,
                     identification = DictionaryType dict methodNames
                   }
     addNewId d tp
     checkVacuous pos dictType
     (_, dictTypeAnn) <- typeChecking True dictType Set 
     let fp = Info{ classifier = abstractMode $ erasePos $ removeVacuousPi dictTypeAnn,
                    identification = DataConstr d
                 }
     addNewId dict fp              
     mapM_ (makeMethod dict methodNames) mths
       where makeMethod constr methodNames (pos, mname, mty) =
               do let names = map getName methodNames
                      Just i = elemIndex (getName mname) names
                      mth = freshNames ("x":names) $ \ (x:mVars) ->
                        LamDict (abst [x] $ LetPat (Var x)
                                  (abst (PApp constr (map Right mVars))
                                   (Var $ mVars !! i)))
                      tyy = erasePos $ removeVacuousPi mty
                  checkVacuous pos tyy
                  (_, tyy') <- typeChecking True tyy Set 
                  (tyy'', a) <- typeChecking False (Pos pos mth) tyy'
                  a' <- erasure a
                  v <- evaluation a'
                  proofChecking False a tyy''
                  let fp = Info{ classifier = abstractMode tyy',
                                 identification = DefinedMethod a v
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
       Just (Right d', args) | getName d' == "Simple" ->
         throwError $ ErrPos pos $ ErrDoc $
         text "Simple class instance is not user-definable."
       Just (Right d', args) | getName d' == "SimpParam" ->
         throwError $ ErrPos pos $ ErrDoc $
         text "SimpParam class instance is not user-definable."
       Just (Right d', args) | getName d' == "Parameter" ->
         throwError $ ErrPos pos $ ErrDoc $
         text "Parameter class instance is not user-definable."         
       Just (Right d', args) ->
         elaborateInstance pos f ty mths


process (Def pos f' ty' def') =
  do checkVacuous pos ty'
     (_, ty) <- typeChecking True ty' Set 
     let ty1 = erasePos $ removeVacuousPi ty
     p <- isParam ty1
     when (not p) $
       throwError $ ErrPos pos (NotParam (Const f') ty')
     let info1 = Info { classifier = ty1,
                        identification = DefinedFunction Nothing}
     addNewId f' info1
     (ty1', ann) <- typeChecking False (Pos pos def') ty1
     -- note: need to do an erasure check before proof checking
     a <- erasure ann
     st <- get
     
     proofChecking False ann ty1'
     v <- evaluation a
       -- trace (show $ dispRaw f' <+> dispRaw ty1' <+> dispRaw (modeSubstitution st) ) $ 
     b <- isBasicValue v
     v' <- if b then typeChecking False (toExp v) ty1' >>= \ x -> return $ Just (snd x)
           else if isCirc v then return $ Just (Const f') else return Nothing
     let info2 = Info { classifier = ty1',
                        identification = DefinedFunction (Just (ann, v, v'))}
     addNewId f' info2

-- This definition without arguments can not be recursive.
process (Defn pos f Nothing def) =
  do (ty, a) <- typeInfering False (Pos pos def)
     let fvs = getVars AllowEigen ty
     when (not $ S.null fvs) $ throwError $ ErrPos pos $ TyAmbiguous (Just f) ty
     checkVacuous pos ty
     p <- isParam ty
     when (not p && not (isConst def)) $
       throwError (ErrPos pos $ NotParam (Const f) ty)
     a' <- erasure a
     proofChecking False a ty
     v <- evaluation a'
     b <- isBasicValue v
     v' <- if b then typeChecking False (toExp v) ty >>= \ x -> return $ Just (snd x)
           else return Nothing
     let fp = Info {classifier = erasePos $ removeVacuousPi ty,
                    identification = DefinedFunction (Just (a, v, v'))
                   }
     addNewId f fp
  where typeInfering b exp =
          do (ty', exp', _) <- typeInfer b exp
             exp'' <- resolveGoals exp'
             r <- updateWithSubst exp''
             ty'' <- resolveGoals ty' >>= updateWithSubst
             let ty''' = unEigen ty''
             ty2 <- updateWithModeSubst ty'''
             return (abstractMode $ booleanVarElim ty2, unEigen r)

process (Defn pos f (Just tt) def) =
  do (_, tt') <- typeChecking True tt Set 
                `catchError` \ e -> throwError $ ErrPos pos e
     let (Forall (Abst [r] ty') Set) = tt'
         ty'' = erasePos ty'
     let info1 = Info { classifier = ty'',
                        identification = DefinedFunction Nothing}
     addNewId f info1
     -- the first check obtain the type information 
     (tk', def0) <- typeChecking''' False (Pos pos def) ty''
     let tk1 = erasePos $ removeVacuousPi tk' 
     let fvs = getVars AllowEigen tk1
     when (not $ S.null fvs) $ throwError $ ErrPos pos $ TyAmbiguous (Just f) tk1
     checkVacuous pos tk1
     p <- isParam tk1
     when (not p && not (isConst def)) $
       throwError (ErrPos pos $ NotParam (Const f) tk1)

     let info2 = Info { classifier = tk1,
                        identification = DefinedFunction Nothing}
     addNewId f info2
     -- the second check
     (tk', def') <- typeChecking False (Pos pos def) tk1
     a' <- erasure def'
     proofChecking False def' tk'
     v <- evaluation a'
     b <- isBasicValue v
     v' <- if b then typeChecking False (toExp v) tk1 >>= \ x -> return $ Just (snd x)
           else return Nothing
     let fp = Info {classifier = tk',
                   identification = DefinedFunction (Just (def', v, v'))
                   }
     addNewId f fp
  where typeChecking''' b exp ty =
          do setInfer True
             (ty', exp', _) <- typeCheck b exp ty
             setInfer False
             exp'' <- updateWithSubst exp'
             r <- resolveGoals exp''
             ty'' <- resolveGoals ty' >>= updateWithSubst
             return (unEigen ty'', unEigen r)

process (Data pos d kd cons) =
  do let constructors = map (\ (_, id, _) -> id) cons
         types = map (\ (_, _, t) -> t) cons
     (_, kd') <- typeChecking True kd Sort 
     dc <- determineClassifier d kd' constructors types
     let tp = Info { classifier = kd',
                     identification = DataType dc constructors Nothing
                   }
     addNewId d tp
     res <- mapM (\ t -> typeChecking True (Pos pos t) Set) types
     let types' = map snd res
     let funcs = map (\ t -> Info{ classifier = erasePos $ removeVacuousPi t,
                                   identification = DataConstr d
                                }) types'
     zipWithM_ addNewId constructors funcs
     generateParamInstance pos dc (Base d) kd' 
       where genEnv :: Int -> [(Maybe Variable, Exp)] -> [(Variable, Exp)]
             genEnv n ((Nothing, e):res) =
               let env = genEnv (n+1) res
               in freshNames [("x"++show n)] $ \ [x] -> (x, e):env
             genEnv n ((Just a, e):res) =
               let env = genEnv n res
               in (a, e):env                                                          
             genEnv n [] = []

             generateParamInstance pos Param d kd' =
               let (bds, _) = flattenArrows kd'
                   env = genEnv 0 bds
                   ns = map fst env
                   head = foldl App d (map Var ns)
                   s = Base (Id "Parameter")
                   ty1 = foldr (\ (x, t) y -> Forall (abst [x] y) t) (App s head) env
               in  do let instId = Id $ "instAt"++ hashPos pos ++ "Parameter"
                      elaborateInstance pos instId ty1 []
             generateParamInstance pos SemiParam d kd' =
               let (bds, _) = flattenArrows kd'
                   s = Base (Id "Parameter")
                   env = genEnv 0 bds
                   env' = filter (\ (x, t) -> isKind t) env
                   ns = map fst env
                   vars = map Var ns
                   head = App s (foldl App d vars)
                   instId = Id $ "instAt"++ hashPos pos ++ "Param"
                   bodies = map (\ v -> App s v) (map (\ x -> Var (fst x)) env')
                   ty1 = foldr (\ (x, t) y -> Forall (abst [x] y) t) (Imply bodies head)
                              env
                   in elaborateInstance pos instId ty1 []
             generateParamInstance _ _ d kd' = return ()

process (Object pos id) =
  do let tp = Info { classifier = Set,
                     identification = DataType Simple [] (Just (ELBase id))
                   }
     addNewId id tp
     let s = Base (Id "Simple")
         sp = Base (Id "SimpParam")
         instId = Id $ "instAt"++ hashPos pos ++ "Simple"
         instPS = Id $ "instAt"++ hashPos pos ++ "SimpParam"
     elaborateInstance pos instId (App s (LBase id)) [] `catchError`
       \ e -> throwError $ addErrPos pos e
     elaborateInstance pos instPS (App (App sp (LBase id)) (Base (Id "Bool"))) [] `catchError`
       \ e -> case e of
                NoDef t | getName t == "Bool" ->
                          throwError $ ErrPos pos SimpParamErr
                _ -> throwError $ addErrPos pos e
               


process (GateDecl pos id params t m) =
  do mapM_ checkParam params
     let (bds, h) = flattenArrows t
     mapM_ checkStrictSimple (h:(map snd bds))
     when (null bds) $ throwError (GateErr pos id)
     let ty = Bang (foldr Arrow t params) m
     (_, tk) <- typeChecking True ty Set
     let gate = makeGate id (map erasePos params) (erasePos t)
     let fp = Info {classifier = erasePos tk,
                   identification = DefinedGate gate
                   }
     addNewId id fp
       where checkParam t =
               do p <- isParam t
                  when (not p) $ throwError $ ErrPos pos (NotAParam t)
             checkStrictSimple (Pos p e) =
               checkStrictSimple e `catchError` \ e -> throwError $ ErrPos p e
             checkStrictSimple (LBase x) = return ()
             checkStrictSimple (Unit) = return ()
             checkStrictSimple (Tensor a b) =
               do checkStrictSimple a
                  checkStrictSimple b
             checkStrictSimple a = throwError (NotStrictSimple a)


process (ControlDecl pos id params t) =
  do mapM_ checkParam params
     let (bds, h) = flattenArrows t
     mapM_ checkSimple (h:(map snd bds))
     when (null bds) $ throwError (GateErr pos id)
     let s = Base $ Id "Simple"
     freshNames ["a"] $ \ (a:[]) ->
       do let head = Tensor h (Var a)
              bds' = (map snd bds)++[Var a]
              t' = foldr Arrow head bds' 
              ty = Bang (Forall (abst [a] (Imply [App s (Var a)]
                                           $ foldr Arrow t' params)) Set)
                   (M (BConst True) (BConst True) (BConst True))
          (_, tk) <- typeChecking True ty Set 
          let gate = makeControl id (map erasePos params) (erasePos t)
          let fp = Info {classifier = erasePos tk,
                        identification = DefinedGate gate
                        }
          addNewId id fp

       where checkParam t =
               do p <- isParam t
                  when (not p) $ throwError $ ErrPos pos (NotAParam t)
             checkSimple (Pos p e) =
               checkSimple e `catchError` \ e -> throwError $ collapsePos p e
             checkSimple (LBase x) = return ()
             checkSimple (Unit) = throwError (NotUnit)
             checkSimple (Tensor a b) =
               do checkSimple a
                  checkSimple b
             checkSimple a = throwError (NotStrictSimple a)


process (SimpData pos d n k0 eqs) = 
  do (_, k2) <- typeChecking True k0 Sort `catchError`
                \ e -> throwError $ collapsePos pos e
     let k = foldr (\ x y -> Arrow Set y) k2 (take n [0 .. ])
     let constructors = map (\ (_, _, c, _) -> c) eqs
         pretypes = map (\ (_, _,_, t) -> t) eqs
         inds = map (\ (_, i,_, _) -> i) eqs
     indx <- checkIndices n d inds `catchError`
             \ e -> throwError $ collapsePos pos e
     info <- mapM (\ (i, t) -> (preTypeToType n k2 i t) `catchError`
                                        \ e -> throwError $ collapsePos pos e)
             (zip inds pretypes)
     let (cs, tys) = unzip info
     checkCoverage d cs `catchError` \ e -> throwError $ collapsePos pos e
     
     let tp1 = Info { classifier = erasePos k,
                      identification = DataType (SemiSimple indx) constructors Nothing
                   }
     addNewId d tp1     
     p <- mapM (\ ty -> typeChecking True ty Set) tys
     let tys' = map snd p
     let funcs = map (\ t -> Info {classifier = erasePos $ unEigen t,
                                  identification = DataConstr d
                                 }
                     ) tys'
     zipWithM_ addNewId constructors funcs

     let s = Base $ Id "Simple"
         s1 = Base $ Id "Parameter"
         sp = Base $ Id "SimpParam"
     tvars <- newNames $ take n (repeat "a")
     tvars' <- newNames $ take n (repeat "b")
     let (bds1, _) = flattenArrows k2
         bds = map snd bds1
     tmvars <- newNames $ take (length bds) (repeat "x")
     let insTy = freshNames tvars $ \ tvs ->
                    freshNames tmvars $ \ tmvs ->
           let env = map (\ t -> (t, Set)) tvs  ++ (zip tmvs bds)
               pre = map (\ x -> App s (Var x)) tvs
               hd = App s $ foldl App (foldl App (LBase d) (map Var tvs))
                    (map Var tmvs)
               ty = foldr (\ (x, t) y -> Forall (abst [x] y) t) (Imply pre hd) env
           in ty
     let insTy' = freshNames tvars $ \ tvs ->
                    freshNames tmvars $ \ tmvs ->
           let env = map (\ t -> (t, Set)) tvs  ++ (zip tmvs bds)
               pre = map (\ x -> App s1 (Var x)) tvs
               hd = App s1 $ foldl App (foldl App (LBase d) (map Var tvs))
                    (map Var tmvs)
               ty = foldr (\ (x, t) y -> Forall (abst [x] y) t) (Imply pre hd) env
           in ty
     let insTy'' =
           freshNames tvars $ \ tvs ->
           freshNames tvars' $ \ tvs' ->
           freshNames tmvars $ \ tmvs ->
           let env = map (\ t -> (t, Set)) tvs ++ map (\ t -> (t, Set)) tvs'  ++ (zip tmvs bds)
               pre = map (\ (x, y) -> App (App sp (Var x)) (Var y)) $ zip tvs tvs'
               hd = App (App sp (foldl App (foldl App (LBase d) (map Var tvs))
                            (map Var tmvs)))
                    (foldl App (foldl App (LBase d) (map Var tvs'))
                      (map Var tmvs))
               ty = foldr (\ (x, t) y -> Forall (abst [x] y) t) (Imply pre hd) env
           in ty
     let instSimp = Id $ "instAt" ++ hashPos pos ++"Simp"
         instParam = Id $ "instAt" ++ hashPos pos ++"Parameter"
         instPS = Id $ "instAt" ++ hashPos pos ++"SimpParam"
     elaborateInstance pos instSimp insTy []
     elaborateInstance pos instParam insTy' []
     elaborateInstance pos instPS insTy'' []
     tfunc <- makeTypeFun n k2 (zip constructors (zip inds tys))
     tfunc' <- erasure tfunc
     let tp = Info {classifier = erasePos k,
                   identification = DataType (SemiSimple indx) constructors
                                    (Just tfunc')
                   }
     addNewId d tp


process (OperatorDecl pos op level fixity) = return ()
process (ImportDecl p mod) = return ()

-- | Check if the defined instance head is overlapping with
-- existing type class instances.
checkOverlap :: Exp -> TCMonad ()
checkOverlap h =
  do es <- get
     let gs = globalInstance $ instanceContext es
     mapM_ helper gs
  where helper (id, exp) =
          let (_, exp') = removePrefixes False exp
              (_, head) = flattenArrows exp'
              (r, _) = runMatch head h
          in if r then throwError $ InstanceOverlap h id exp
             else return ()


-- | Construct an instance function. The argument /f'/ is 
-- the name of the instance function and /ty/ is its type. The
-- arguments /mths/ are the method definitions.
elaborateInstance :: Position -> Id -> Exp -> [(Position, Id, Exp)] -> TCMonad ()
elaborateInstance pos f' ty mths =
  do annTy <- typeChecking' True ty Set
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
            let (bds, _) = flattenArrows constTy'
            freshNames names $ \ ns ->    
              do let instEnv = zip ns (map snd bds0)
                 -- add the name of instance function and its type to the
                 -- global instance context, this enable recursive dictionary
                 -- construction.
                 addGlobalInst f' annTy
                 -- Type check and elaborate each method
                 ms' <- zipWithM (helper env instEnv) mths (map snd bds)
                 -- construct the annotated version of the instance function.
                 let def = foldl App (foldl AppType (Const c) args) ms'
                     def' = unEigen $ if null ns then rebind env def
                                      else rebind env $ LamDict (abst ns def)
                     annTy' = erasePos annTy
                 def'' <- erasure def'
                 v <- evaluation def''
                 let fp = Info { classifier = annTy',
                                 identification = DefinedInstFunction def' v
                              }
                 addNewId f' fp
                 proofChecking False def' annTy'
                 
       _ -> throwError $ ErrPos pos $ TypeClassNotValid h                 
       where instantiateWith (Forall (Abst vs b') t) xs =
               let xs' = drop (length vs) xs
                   b'' = apply (zip vs xs) b'
               in instantiateWith b'' xs'
             instantiateWith (Mod (Abst _ t)) xs = instantiateWith t xs
             instantiateWith t xs = t
             helper env instEnv (p, _, m) t =
               let env' = map (\ x -> case x of
                                        (Just y, a) -> (y, a)
                                  ) env
               in 
                 do mapM_ (\ (x, t) -> addVar x t) env'
                    mapM_ (\ (x, t) -> insertLocalInst x t) instEnv
                    updateParamInfo (map snd instEnv)
                    (t', a) <- typeChecking'' (map fst env') False (Pos p m) (erasePos t)
                    mapM_ (\ (x, t) -> removeVar x) env'
                    mapM_ (\ (x, t) -> removeLocalInst x) instEnv
                    return a 

             rebind [] t = t
             rebind ((Just x, ty):res) t | isKind ty = LamType (abst [x] (rebind res t))
             rebind ((Just x, ty):res) t | otherwise = LamTm (abst [x] (rebind res t))
             -- A version of type checking that avoids checking forall param. 
             typeChecking' b exp ty =
               do setCheckBound False
                  (ty', exp', _) <- typeCheck b exp ty
                  setCheckBound True
                  exp'' <- updateWithSubst exp'
                  r <- resolveGoals exp''
                  return (unEigen r)
             -- a version of typeChecking that uses unEigenBound instead of unEigen
             typeChecking'' vars b exp ty =
               do (ty', exp', _) <- typeCheck b exp ty
                  exp'' <- resolveGoals exp'
                  r <- updateWithSubst exp''
                  ty'' <- resolveGoals ty' >>= updateWithSubst
                  return (unEigenBound vars ty'', unEigenBound vars r)
  
-- | Determine the classifier for a data type declaration.
determineClassifier :: Id -> Exp -> [Id] -> [Exp] -> TCMonad DataClassifier
determineClassifier d kd constructors types =
  do f <- queryParam d kd constructors types
     if f then return Param
       else do g <- querySemiParam d kd constructors types
               if g then return SemiParam
                 else return Unknown
  where queryParam d kd constructors types = 
          do let tp = Info{classifier = kd,
                          identification = DataType Param constructors Nothing
                          }
             addNewId d tp
             r <- mapM helper types
             return $ and r
               where helper ty =
                       do let (_, ty') = removePrefixes True ty
                              (args, h) = flattenArrows ty'
                          r <- mapM isParam (map snd args)
                          return $ and r
        querySemiParam d kd constructors types = 
          do let tp = Info{classifier = kd,
                          identification = DataType SemiParam constructors Nothing
                          }
             addNewId d tp
             r <- mapM helper types
             return $ and r
               where helper ty =
                       do let (_, ty') = removePrefixes True ty
                              (args, h) = flattenArrows ty'
                          r <- 
                               mapM (\ a ->
                                        do r1 <- isParam a
                                           r2 <- isSemiParam a
                                           return (r1 || r2)
                                    ) (map snd args)
                          return $ and r

-- | Construct a gate from a gate declaration.
makeGate :: Id -> [Exp] -> Exp -> Value
makeGate id ps t =
  let lp = length ps + 1
      ns = getName "x" lp
      (inss, outExp) = makeInOut t
      outNames = size outExp
      inExp = if null inss then VUnit
                else foldl VTensor (head inss) (tail inss)
      inNames = size inExp
  in
      freshNames ns $ \ (y:xs) ->
      freshLabels inNames $ \ ins ->
      freshLabels outNames $ \ outs ->
      let params = map VVar xs
          inExp' = toVal inExp ins
          outExp' = toVal outExp outs
          g = Gate id params inExp' outExp' VStar
          morph = Wired $ abst (ins ++ outs) (VCircuit $ Morphism inExp' [g] outExp')
          env = Map.fromList [(y, (morph, 1))] 
          unbox_morph = ELam [y] $ etaPair (length inss) (EForce $ EApp EUnBox (EVar y))
          res = VLiftCirc (abst xs (abst env unbox_morph))
      in res
  where makeInOut (Arrow t t') =
          let (ins, outs) = makeInOut t'
          in (toV t:ins, outs)
        makeInOut (Pos p e) = makeInOut e
        makeInOut a = ([], toV a)
        toV Unit = VUnit
        toV (Tensor a b) = VTensor (toV a) (toV b)
        toV (LBase x) = VLBase x
        getName x lp =
          let xs = x:xs
          in zipWith (\ x y -> x ++ show y) (take lp xs) [0 .. ]
          
        etaPair n e | n == 0 = error "from etaPair"
        etaPair n e =
          freshNames (getName "y" n) $ \ xs ->
          let xs' = map EVar xs
              pairs = foldl EPair (head xs') (tail xs')
          in abst (zip xs $ repeat 1) (EApp e pairs)

-- | Construct a generic controlled gate from a controlled declaration.
makeControl :: Id -> [Exp] -> Exp -> Value
makeControl id ps t =
  let lp = length ps + 1
      ns = getName "x" lp
      (inss, outExp) = makeInOut t
      outNames = size outExp
      inExp = if null inss then VUnit
                else foldl VTensor (head inss) (tail inss)
      inNames = size inExp
  in
      freshNames ("dict":"ctrl":ns) $ \ (d:c:y:xs) ->
      freshLabels inNames $ \ ins ->
      freshLabels outNames $ \ outs ->
      let params = map VVar xs
          inExp' = toVal inExp ins
          outExp' = toVal outExp outs
          g = Gate id params inExp' outExp' (VVar c)
          morph = Wired $ abst (ins ++ outs) (VCircuit $ Morphism inExp' [g] outExp')
          env = Map.fromList [(y, (morph, 1))] 
          unbox_morph = etaPair (length inss) (EForce $ EApp EUnBox (EVar y)) c
          res = open unbox_morph $ \ ys m ->
              VLiftCirc $ abst ((d:xs)++ys ++ [c]) (abst env m)
      in res
  where makeInOut (Arrow t t') =
          let (ins, outs) = makeInOut t'
          in (toV t:ins, outs)
        makeInOut (Pos p e) = makeInOut e
        makeInOut a = ([], toV a)
        toV Unit = VUnit
        toV (Tensor a b) = VTensor (toV a) (toV b)
        toV (LBase x) = VLBase x
        getName x lp =
          let xs = x:xs
          in zipWith (\ x y -> x ++ show y) (take lp xs) [0 .. ]
          
        etaPair n e c | n == 0 = error "from etaPair"
        etaPair n e c =
          freshNames (getName "y" n) $ \ xs ->
          let xs' = map EVar xs
              pairs = foldl EPair (head xs') (tail xs')
          in (abst xs (EPair (EApp e pairs) (EVar c))) 


-- | Make a type function for runtime labels generation. The input /n/
-- is the number of type variables, /k0/ is the kind annotation. 
makeTypeFun :: Int -> Exp -> [(Id, (Maybe Int, Exp))] -> TCMonad Exp
makeTypeFun n k0 ((c, (Nothing, ty)):[]) =
     let (env, m) = removePrefixes False ty
         vars = map (\ (Just x , _) -> x) env
         (bds, h) = flattenArrows m
         bds' = map snd bds
         exp = foldl App (Const c) bds'
         t = if null vars then exp else Lam (abst vars exp) 
     in return t


makeTypeFun n k0 xs@((_, (Just i, _)):_) =
  do tyvars <- newNames $ take n (repeat "a")
     let (bds, _) = flattenArrows k0
     tmvars <- newNames $ take (length bds) (repeat "x")
     freshNames tyvars $ \ tvars ->
       freshNames tmvars $ \ mvars ->
       let (tmv1, cv:tmv2) = splitAt i mvars
           bindings = map (helper $ tvars ++ tmv1 ++ tmv2) xs
           vs = tvars++tmv1++(cv:tmv2)
           exp = Lam (abst vs $ Case (Var cv) (B bindings)) 
       in return exp
       where helper vss (c, (Just i, ty)) =
               let (env, m) = removePrefixes False ty
                   (bds, h) = flattenArrows m
               in case flatten h of
                   Just (Right w, args) ->
                     let (ttvars, pat:mmvars) = splitAt (n + i) args
                         renamings = zip (map getVar ttvars ++ map getVar mmvars) (map Var vss)
                         rhs = apply renamings $ foldl App (Const c) (map snd bds)
                         r = abst (toPat pat) rhs
                     in r 
                   Nothing -> error $ show (text "from makeTypeFun helper:" <+> disp h)
                
             getVar (Var x) = x
             getVar (Pos p e) = getVar e
             getConst (Const x) = x
             getConst (Pos p e) = getConst e
             toPat p = let (h, as) = unwind AppFlag p
                       in PApp (getConst h) (map (\ a -> Right (getVar a)) as)

-- | Check an expression against a type. It is a wrapper on the 'typeCheck' function.
typeChecking :: Bool -> Exp -> Exp -> TCMonad (Exp, Exp)
typeChecking b exp ty =
  do (ty', exp', _) <- typeCheck b exp ty
     exp'' <- resolveGoals exp'
     r <- updateWithSubst exp''
     ty'' <- resolveGoals ty' >>= updateWithSubst
     let ty''' = unEigen ty''
     ty2 <- updateWithModeSubst ty'''
     return (abstractMode $ booleanVarElim ty2, unEigen r)


-- | Check an annotated expression against a type. It is a wrapper on 'proofCheck' function.

proofChecking :: Bool -> Exp -> Exp -> TCMonad ()
proofChecking b exp ty =
  proofCheck b exp ty `catchError` \ e -> throwError $ PfErrWrapper exp e ty


