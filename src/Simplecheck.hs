module Simplecheck where



-- | Make sure the pattern matching is on the same argument in the simple type declaration.
-- The first argument is the length of the type arguments.  
checkIndices :: Int -> Id -> [Maybe Int] -> TCMonad (Maybe Int)
checkIndices n d ls =
  case sequence ls of
    Nothing -> 
      do when (length ls > 1) $ throwSimple $ Ambiguous d
         return Nothing
    Just (i:inds) -> helper i inds >> return (Just (n+i))
  where helper :: Int -> [Int] -> TCMonad ()       
        helper i (j:res) =
          if j /= i then throwSimple $ IndexInconsistent (n+i) (n+j) d
          else helper i res
        helper i [] = return ()

-- | Check the coverage of the pattern matching in the simple declaration.
checkCoverage :: Id -> [Maybe Id] -> TCMonad ()
checkCoverage d' cons =
  case sequence cons of
    Nothing ->
      do when (length cons > 1) $ throwSimple $ Ambiguous d'
         return ()
    Just css@(c:cs) ->
      do funPac <- lookupConst c
         let (DataConstr d) = identification funPac
         typePac <- lookupConst d
         let DataType _ cons _ = identification typePac
         when (length css /= length cons) $ throwSimple $ CoverErr css cons d'
         when (not $ null (css \\ cons)) $ throwSimple (CoverErr css cons d')

preTypeToType :: Int -> Exp -> Maybe Int -> Exp -> TCMonad (Maybe Id, Exp)
preTypeToType n k i (Pos p e) =
  preTypeToType n k i e `catchError` \ e -> throwError $ collapsePos p e
preTypeToType n k i (Lam (Abst vs m) _) =
  handleBody n k i m 
preTypeToType n k i (Forall (Abst vs m) ty) =
  do (c, t) <- preTypeToType n k i m
     return (c, Forall (abst vs t) ty)
preTypeToType n k i a = handleBody n k i a

-- | The helper function for preTypeToType that does the real work of the conversion.
handleBody n k i m =
  do let (bds, h) = deCompose m
         Just (Right hid, args) = getId h
         (argTypes, _) = deCompose k
     mapM_ (checkBody h hid) bds
     case i of
       Just j -> 
         let (vsTy, pT:resTy) = splitAt j argTypes
             (vs, p:res) = splitAt j (drop n args)
             Just (id, pargs) = getId p in
           case id of
             Left pid ->
               do (vs', pargs', res') <- checkVars vs pargs res
                  pidTy <- lookupConst pid >>= \ x -> return $ classifier x
                  let pargTys = instantiation pT pidTy
                        -- deCompose pidTy'
                      pPair = zip pargs' pargTys
                      vsPair = zip vs' vsTy
                      resPair = zip res' resTy
                      finalArgs = vsPair ++ pPair ++ resPair
                      finalType = foldr (\ (x, t) y -> Forall (abst [x] y) t) m finalArgs 
                  return (Just pid, finalType)
             Right pid ->
               throwError $ withPosition p (SimpCheck (TConstrErr pid)) 
       Nothing ->
         do (_, args',_) <- checkVars [] (drop n args) []
            let finalArgs = zip args' argTypes
                finalType = foldr (\ (x, t) y -> Forall (abst [x] y) t) m finalArgs 
            return (Nothing, finalType)
       where getVar :: Exp -> TCMonad Variable
             getVar (Var x) = return x
             getVar (Pos p e) = getVar e `catchError` \ e -> throwError $ collapsePos p e
             getVar a = throwError $ SimpCheck (NonSimplePatErr a)
             checkVars vs pargs res =
               do vs' <- mapM getVar vs
                  pargs' <- mapM getVar pargs
                  res' <- mapM getVar res
                  return (vs', pargs', res')
             instantiation head ty =
               let (env, t) = decomposeForall ty
                   (argTs, h') = deCompose t
                   (r, s) = runMatch h' head
               in if r then
                    let argTs' = map (apply s) argTs
                    in argTs'
                    else error $ "can't match " ++ (show $ disp h') ++ "against " ++ (show $ disp head)

-- | check the right hand side of the simple declaration is well-defined.
checkBody h id (Pos p e) = checkBody h id e `catchError` \ e -> throwError $ collapsePos p e
checkBody h id (Var x) = return ()
checkBody h id b | Nothing <- getId b = error $ "from checkBody:" ++ (show (disp b))
checkBody h id b | Just (Right kid, args) <- getId b =
  if kid == id then 
    let b' = erasePos b
        h' = erasePos h
        s1 = b' `isSubterm` h'
        s2 = b' /= h'
    in if s1 && s2 then return ()
       else throwSimple $ SubtermErr b h
  else do x <- semiSimple b
          when (not x) $ throwSimple (NotSimple b)
checkBody h id b | Just (Left kid, args) <- getId b =
  throwSimple (ConstrErr kid)

-- | First order subterm relation.
isSubterm (App t1 t2) (App t3 t4) =
  isSubterm t1 t3 && isSubterm t2 t4
isSubterm (Var x) (Var y) | x == y = True
isSubterm (Const x) (Const y) | x == y = True
isSubterm (Base x) (Base y) | x == y = True 
isSubterm (LBase x) (LBase y) | x == y = True 
isSubterm (Var x) t =
  let fv = free_vars NoEigen t
  in x `elem` fv
isSubterm u v = False

-- checkIndices = undefined

-- preTypeToType = undefined


-- checkCoverage = undefined
