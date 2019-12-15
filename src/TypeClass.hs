module TypeClass where

import Utils
import Syntax
import Nominal
import TCMonad

resolveGoals :: Exp -> TCMonad Exp
-- resolveGoals a | trace (show $ text "resolveGoals:" <+> disp a) False = undefined
resolveGoals a = undefined
