module TypeClass where

import Utils
import Syntax
import Nominal
import TCMonad
import Substitution
import Normalize
import TypeError
import SyntacticOperations

import Control.Monad.Except
import Control.Monad.State
import qualified Data.Set as S


resolveGoals :: Exp -> TCMonad Exp
-- resolveGoals a | trace (show $ text "resolveGoals:" <+> disp a) False = undefined
resolveGoals a = 
  do ts <- get
     let env = instanceContext ts
         goals = goalInstance env
         subs = subst ts
         goals' = map (\ (x, (t, e)) -> (x, (substitute subs t, e))) goals
         goalVars = getVars GetGoal a
         goals'' = [ (x, (t, e)) | (x, (t, e)) <- goals', x `S.member` goalVars]
     if (not (S.null goalVars)) then helper a goals''
       else  return a
       
  where helper ann [] = return ann
        helper ann ((x, (t, e)):xs) = 
          do t' <- resolveInst t `catchError`
                   \ er -> throwError (Originated e er)
             let ann' = apply [(x, t')] ann
             helper ann' xs
        resolveInst e =
          do ts <- get
             let env = instanceContext ts
                 local = localInstance env
                 gl = globalInstance env
             resolution e local gl



resolution :: Exp -> [(Variable, Exp)] -> [(Id, Exp)] -> TCMonad Exp
resolution goal localEnv globalEnv =
  do goal' <- normalize goal
     (t, newGoals) <- rewrite goal' localEnv globalEnv
     helper t newGoals
       where helper t [] = return t
             helper t ((x, subGoal):res) =
               do t' <- resolution subGoal localEnv globalEnv
                  let t'' = apply [(x, t')] t
                  helper t'' res


rewrite goal localEnv globalEnv =
  do r <- tryLocal goal localEnv
     case r of
       Just (x, t) -> return (Var x, [])
       Nothing -> tryGlobal goal globalEnv
       where tryLocal goal [] = return Nothing
             tryLocal goal ((x, t):xs) =
               do let (res, sub) = runMatch t goal
                  if res then return $ Just (x, t)
                    else tryLocal goal xs
             tryGlobal goal [] =
               throwError $ ResolveErr goal
             tryGlobal goal ((k, t):xs) =
               do let (vs, t') = decomposeForall' t
                      (bds, h) = flattenArrows t'
                      (r, subs) = runMatch h goal
                  if r then
                    do let bds' = map (apply subs) bds
                           vs' = map (\ a -> case a of
                                         Left (x, t) -> Left (apply subs (Var x) , t)
                                         Right (x, t) -> Right (apply subs (Var x) , t)
                                       ) vs
                           e = makeApp (Const k) vs'
                       ns <- mapM (\ x -> newName "newGoal") bds'
                       let newGoals = zip ns bds'
                           e' = foldl AppDict e (map Var ns)
                       return (e', newGoals)
                    else tryGlobal goal xs
             makeApp h (Right (t, ty):res) | isKind ty = makeApp (AppType h t) res
             makeApp h (Right (t, ty):res) | otherwise = makeApp (AppTm h t) res
             makeApp h (Left (t, ty):res) = makeApp (AppImp h t) res
             makeApp h [] = h
             newName :: String -> TCMonad Variable
             newName s =
               do r <- newNames [s]
                  freshNames r $ \ (s':[]) -> return s'


-- | Match the first expression against the second, return the result and the substitution.
runMatch :: Exp -> Exp -> (Bool, [(Variable, Exp)])
runMatch e1 e2 = runState (match (erasePos e1) (erasePos e2)) []

-- | Type class resolution requires a matching algorithm instead of unification.
match :: Exp -> Exp -> State [(Variable, Exp)] Bool
match Unit Unit = return True
match (Base x) (Base y) | x == y = return True
                        | otherwise = return False
match (LBase x) (LBase y) | x == y = return True
                          | otherwise = return False
match (Const x) (Const y) | x == y = return True
                          | otherwise = return False

match (EigenVar x) (EigenVar y) | x == y = return True
                                | otherwise = return False

-- Note that matching will need to check consistency of the substitution.
match (Var x) t =
  do s <- get
     case lookup x s of
       Nothing -> modify (\ s -> (x, t):s) >> return True
       Just t' | t == t' -> return True
               | otherwise -> return False

match (Force' t) (Force' t') = match t t'
match (Lift t) (Lift t') = match t t'
match (Bang t) (Bang t') = match t t'

match (App t1 t2) (App t3 t4) =
  do r <- match t1 t3
     if r then match t2 t4
       else return False

match (App' t1 t2) (App' t3 t4) =
  do r <- match t1 t3
     if r then match t2 t4
       else return False

match (AppType t1 t2) (AppType t3 t4) =
  do r <- match t1 t3
     if r then match t2 t4
       else return False

match (AppDep t1 t2) (AppDep t3 t4) =
  do r <- match t1 t3
     if r then match t2 t4
       else return False

match (AppDict t1 t2) (AppDict t3 t4) =
  do r <- match t1 t3
     if r then match t2 t4
       else return False

match (AppTm t1 t2) (AppTm t3 t4) =
  do r <- match t1 t3
     if r then match t2 t4
       else return False


match (Tensor t1 t2) (Tensor t3 t4) =
  do r <- match t1 t3
     if r then match t2 t4
       else return False

match (Circ t1 t2) (Circ t3 t4) =
  do r <- match t1 t3
     if r then match t2 t4
       else return False

match a b = return False
