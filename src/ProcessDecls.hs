{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module ProcessDecls where

import TCMonad
import Syntax
import SyntacticOperations
import Utils
import TypeError
import Typechecking
import Proofchecking
import Evaluation
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


process :: Decl -> TCMonad ()
process (Class pos d kd dict dictType mths) = 
  do let methodNames = map (\(_, s, _, _) -> s) mths
         tp = Info { classifier = erasePos kd,
                     identification = DictionaryType dict methodNames
                   }
     addNewId d tp
     checkVacuous pos dictType
     dictTypeAnn <- typeChecking True dictType Set 
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
                  ty'' <- typeChecking True ty' Set
                  tyy' <- typeChecking True tyy Set 
                  a <- typeChecking False (Pos pos mth) (unEigen ty'')
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
     ty <- typeChecking True ty' Set 
     let ty1 = erasePos $ removeVacuousPi ty
     p <- isParam ty1
     when (not p) $
       throwError $ ErrPos pos (NotParam (Const f') ty')
     let info1 = Info { classifier = ty1,
                        identification = DefinedFunction Nothing}
     addNewId f' info1
     ann <- typeChecking False (Pos pos def') ty1
     a <- erasure ann
     v <- evaluation a
     -- annV <- typeChecking False v ty1
     let info2 = Info { classifier = ty1,
                        identification = DefinedFunction (Just (ann, v))}
     addNewId f' info2

process (Data pos d kd cons) =
  do let constructors = map (\ (_, id, _) -> id) cons
         types = map (\ (_, _, t) -> t) cons
     kd' <- typeChecking True kd Sort 
     dc <- determineClassifier d kd' constructors types
     let tp = Info { classifier = kd',
                     identification = DataType dc constructors Nothing
                   }
     addNewId d tp
     types' <- mapM (\ t -> typeChecking True (Pos pos t) Set) types
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
                     identification = DataType Simple [] (Just (LBase id))
                   }
     addNewId id tp
     let s = Base (Id "Simple")
         sp = Base (Id "SimpParam")
         instId = Id $ "instAt"++ hashPos pos ++ "Simple"
         instPS = Id $ "instAt"++ hashPos pos ++ "SimpParam"
     elaborateInstance pos instId (App s (LBase id)) []
     elaborateInstance pos instPS (App (App sp (LBase id)) (Base (Id "Bool"))) []


process (GateDecl pos id params t) =
  do mapM_ checkParam params
     let (bds, h) = flattenArrows t
     mapM_ (\ x -> checkStrictSimple x) (h:(map snd bds))
     when (null bds) $ throwError (GateErr pos id)
     let ty = Bang $ foldr Arrow t params
     tk <- typeChecking True ty Set
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


process (SimpData pos d n k0 eqs) = -- [instSimp, instParam, instPS]
  do -- defaultToElab $ ensureArrowKind k0
     -- defaultToElab $ checkRegular k0
     k2 <- typeChecking True k0 Sort 
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
     tys' <- mapM (\ ty -> typeChecking True ty Set) tys

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
     let tp = Info {classifier = erasePos k,
                   identification = DataType (SemiSimple indx) constructors (Just tfunc)
                   }
     addNewId d tp


process (OperatorDecl pos op level fixity) = return ()
process (ImportDecl p mod) = return ()


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
                     def' = if null ns then rebind env def
                            else rebind env $ LamDict (abst ns def)
                     annTy' = erasePos annTy
                 def'' <- erasure def'
                 let fp = Info { classifier = annTy',
                                identification = DefinedInstFunction def' def''
                              }
                 addNewId f' fp

       _ -> throwError $ ErrPos pos $ TypeClassNotValid h                 
       where instantiateWith (Forall (Abst vs b') t) xs =
               let subs = zip vs xs
                   xs' = drop (length vs) xs
               in instantiateWith (apply subs b') xs'
             instantiateWith t xs = t
             helper env instEnv (p, _, m) t =
               let env' = map (\ x -> case x of
                                        (Just y, a) -> (y, a)
                                  ) env
               in -- typeCheckWithEnv env' instEnv (Pos p m) (erasePos t)
                 do mapM_ (\ (x, t) -> addVar x t) env'
                    mapM_ (\ (x, t) -> insertLocalInst x t) instEnv
                    updateParamInfo (map snd instEnv)
                    a <- typeChecking False (Pos p m) (erasePos t)
                    -- a' <- resolveGoals a
                    mapM_ (\ (x, t) -> removeVar x) env'
                    mapM_ (\ (x, t) -> removeLocalInst x) instEnv
                    return $ a -- unEigen a'
                    

             rebind [] t = t
             rebind ((Just x, ty):res) t | isKind ty = LamType (abst [x] (rebind res t))
             rebind ((Just x, ty):res) t | otherwise = LamTm (abst [x] (rebind res t))


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

makeGate :: Id -> [Exp] -> Exp -> Exp
makeGate id ps t =
  let lp = length ps
      ns = getName "x" lp
      (inss, outExp) = makeInOut t
      outNames = genNames outExp
      inExp = if null inss then Unit
                else foldl Tensor (head inss) (tail inss)
      inNames = genNames inExp
  in
      freshNames ns $ \ xs ->
      freshNames inNames $ \ ins ->
      freshNames outNames $ \ outs ->
      let params = map Var xs
          inExp' = toVal inExp ins
          outExp' = toVal outExp outs
          g = Gate id params inExp' outExp' Star
          morph = Wired $ abst (ins ++ outs) (Morphism inExp' [g] outExp')
          m =  App UnBox
                        (Let morph (freshNames ["y"] $ \ (y:[]) -> abst y (Var y)))
          unbox_morph = etaPair (length inss) m
          res = if null xs then unbox_morph
                else
                  case unbox_morph of
                       Lam bd ->
                         open bd $ \ ys m -> Lam (abst (xs++ys) m) 
                       _ -> Lam (abst xs unbox_morph) 
      in res
  where makeInOut (Arrow t t') =
          let (ins, outs) = makeInOut t'
          in (t:ins, outs)
        makeInOut (Pos p e) = makeInOut e
        makeInOut a = ([], a)
        getName x lp =
          let xs = x:xs
          in zipWith (\ x y -> x ++ show y) (take lp xs) [0 .. ]
          
        etaPair n e | n == 0 = App e Star
        etaPair n e =
          freshNames (getName "y" n) $ \ xs ->
          let xs' = map Var xs
              pairs = foldl Pair (head xs') (tail xs')
          in Lam $ abst xs (App e pairs)


-- | Make a type function for runtime wires generation.
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


typeChecking b exp ty =
  do (ty', exp') <- typeCheck b exp ty
     exp'' <- updateWithSubst exp'
     r <- resolveGoals exp''
     return $ unEigen r

-- | a version of type checking for elaborateInstance
typeChecking' b exp ty =
  do setCheckBound False
     (ty', exp') <- typeCheck b exp ty
     setCheckBound True
     exp'' <- updateWithSubst exp'
     r <- resolveGoals exp''
     return $ unEigen r

