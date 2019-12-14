module Typechecking where

import Syntax
import TCMonad
import TypeError

import Control.Monad.Except


-- | The flag indicate if whether it is during kinding or not.
typeCheck :: Bool -> Exp -> Exp -> TCMonad (Exp, Exp)
typeInfer :: Bool -> Exp -> TCMonad (Exp, Exp)

typeInfer flag (Pos p e) =
  do (ty, ann) <- typeInfer flag e `catchError` \ e -> throwError $ addErrPos p e
     return (ty, (Pos p ann))

typeInfer flag Set = return (Sort, Set)

typeInfer flag a@(Base kid) =
  lookupId kid >>= \ x -> return (classifier x, a)

typeInfer flag a@(Var x) =
  do (t, _) <- lookupVar x
     if flag then
       do t' <- shape t 
          return (t', a)
       else
       do updateCount x
          return (t, a)






typeCheck flag (Pos p e) ty =
  do (ty', ann) <- typeCheck flag e ty `catchError` \ e -> throwError $ addErrPos p e
     return (ty', Pos p ann)

