module Unification where

runUnify :: Exp -> Exp -> Maybe Subst
runUnify t1 t2 =
  let t1' = erasePos t1
      t2' = erasePos t2
      (r, s) = runState (unify t1' t2') Map.empty
  in if r then Just s else Nothing


unify Unit Unit = return True
unify Set Set = return True
unify (Base x) (Base y) | x == y = return True
                        | otherwise = return False
unify (LBase x) (LBase y) | x == y = return True
                          | otherwise = return False
unify (Const x) (Const y) | x == y = return True
                          | otherwise = return False


unify (EigenVar x) (EigenVar y) | x == y = return True
                                | otherwise = return False


unify f (Var x) t
  | Var x == t = return True
  | x `S.member` free_vars AllowEigen t = return False
  | otherwise = 
    do sub <- get
       let subst' = mergeSubL [(x, t)] sub
       put subst'
       return True

unify f t@(EigenVar y) (Var x) = 
    do sub <- get
       let subst' = mergeSubL [(x, t)] sub
       put subst'
       return True

unify f t (Var x)
  | Var x == t = return True
  | x `S.member` free_vars AllowEigen t = return False
  | otherwise =
    do sub <- get
       let subst' = mergeSubL [(x, t)] sub
       put subst'
       return True

-- In Eigen mode, when unifying (EigenVar x) and Var y where x != y,
-- we always generate substitution y |-> (EigenVar x). The full consequence
-- of this decision may be subtle. But my intention is to make eigenvariable
-- more stable so that they can only be substitue when dependent pattern matching
-- happen.       
       
unify Eigen (EigenVar x) t 
  | EigenVar x == t = return True
  | x `S.member` free_vars AllowEigen t = return False
  | otherwise =
        do sub <- get
           let subst' = mergeSubL [(x, t)] sub
           put subst'
           return True

unify Eigen t (EigenVar x)
  | EigenVar x == t = return True
  | x `S.member` free_vars AllowEigen t = return False                      
  | otherwise = 
        do sub <- get
           let subst' = mergeSubL [(x, t)] sub
           put subst'
           return True

unify f (GoalVar x) t
  | GoalVar x == t = return True
  | x `S.member` free_vars GetGoal t = return False
  | otherwise = 
    do sub <- get
       let subst' = mergeSubL [(x, t)] sub
       put subst'
       return True

unify f t (GoalVar x) 
  | GoalVar x == t = return True
  | x `S.member` free_vars GetGoal t = return False
  | otherwise = 
    do sub <- get
       let subst' = mergeSubL [(x, t)] sub
       put subst'
       return True


-- We allow unifying two first-order existential types.  
unify f (Exists (Abst x m) ty1) (Exists (Abst y n) ty2) =
  do r <- unify f ty1 ty2
     if r then with_fresh_namedV "#existUnif" $ \ e ->
       do let m' = apply [(x, EigenVar e)] m
              n' = apply [(x, EigenVar e)] n
          sub <- get
          unify f (substitute sub m') (substitute sub n')
       else return False

-- We also allow unifying two case expression
unify f (Case e1 (B br1)) (Case e2 (B br2)) | br1 == br2 =
  unify f e1 e2
     
     
unify f (Arrow t1 t2) (Arrow t3 t4) =
  do a <- unify f t1 t3
     if a
       then do sub <- get
               unify f (substitute sub t2) (substitute sub t4)
       else return False

unify f (Arrow' t1 t2) (Arrow' t3 t4) =
  do a <- unify f t1 t3
     if a
       then do sub <- get
               unify f (substitute sub t2) (substitute sub t4)
       else return False

unify f (Tensor t1 t2) (Tensor t3 t4) =
  do a <- unify f t1 t3
     if a
       then do sub <- get
               unify f (substitute sub t2) (substitute sub t4)
       else return False

unify f (Circ t1 t2) (Circ t3 t4) =
  do a <- unify f t1 t3
     if a
       then do sub <- get
               unify f (substitute sub t2) (substitute sub t4)
       else return False

unify f (Bang t) (Bang t') = unify f t t'
-- unify f (Force t) (Force t') = unify f t t'
unify f (Force' t) (Force' t') = unify f t t'
unify f (Lift t) (Lift t') = unify f t t'

unify f (App t1 t2) (App t3 t4) =
  do a <- unify f t1 t3
     if a
       then
       do sub <- get
          unify f (substitute sub t2) (substitute sub t4)
       else return False

unify f (App' t1 t2) (App' t3 t4) =
  do a <- unify f t1 t3
     if a
       then
       do sub <- get
          unify f (substitute sub t2) (substitute sub t4)
       else return False

unify f (AppDict t1 t2) (AppDict t3 t4) =
  do a <- unify f t1 t3
     if a
       then
       do sub <- get
          unify f (substitute sub t2) (substitute sub t4)
       else return False

unify f (AppDep t1 t2) (AppDep t3 t4) =
  do a <- unify f t1 t3
     if a
       then
       do sub <- get
          unify f (substitute sub t2) (substitute sub t4)
       else return False

-- unify f (AppImp t1 t2) (AppImp t3 t4) =
--   do a <- unify f t1 t3
--      if a
--        then
--        do sub <- get
--           unify f (substitute sub t2) (substitute sub t4)
--        else return False

unify f (AppType t1 t2) (AppType t3 t4) =
  do a <- unify f t1 t3
     if a
       then do sub <- get
               unify f (substitute sub t2) (substitute sub t4)
       else return False

unify f (AppTm t1 t2) (AppTm t3 t4) =
  do a <- unify f t1 t3
     if a
       then do sub <- get
               unify f (substitute sub t2) (substitute sub t4)
       else return False


unify f t t' = return False



