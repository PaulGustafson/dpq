module TypeError where

import Utils
import Syntax
import qualified ConcreteSyntax as C


import Nominal
import Prelude hiding ((<>))
import Text.PrettyPrint
import Control.Monad.Except


data TypeError = Unhandle Exp
               | ErrPos Position TypeError
               | NoDef Id


instance Disp TypeError where
  display flag (ErrPos p e) =
    display flag p $$   
    display flag e

  display flag (Unhandle t) =
    text "there is no type inference rule to infer a type for the expresson:" $$
    nest 2 (display flag t)

  display flag (NoDef t) =
    text "no definition for the identifier:" $$ nest 2 (display flag t)


