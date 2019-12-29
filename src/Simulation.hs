module Simulation where

import SyntacticOperations hiding (toBool)
import Syntax
import Utils


import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.State
import Control.Monad.Except
import Text.PrettyPrint

import Debug.Trace
-- * A simulator for classical circuits

type Simulate a = ExceptT SimulateError (State (Map Variable Bool)) a

data SimulateError =
  NotSupported String
  | AssertionErr Variable Bool Bool
  | WrapGates [Gate] SimulateError
  deriving Show
instance Disp Bool where
  display _ True = text "1"
  display _ False = text "0"
  
instance Disp SimulateError where
  display flag (NotSupported s) =
    text "simulator currently does not support simulating gate:" <+> text s

  display flag (AssertionErr x exp act) =
    text "assertion error on label:" <+> dispRaw x $$
    text "expecting value:" <+> display flag exp $$
    text "actual value:" <+> display flag act

  display flag (WrapGates gs e) =
    display flag e $$
    text "when running the simulation for the circuit:" $$
    vcat (map (display flag) gs)
    
makeValueMap :: Exp -> Exp -> Map Variable Bool
makeValueMap Star Star = Map.empty
makeValueMap (Const x) (Const y) | x == y = Map.empty
makeValueMap (Label l) a@(Const x) =
  Map.fromList [(l, toBool a)]
  
makeValueMap (Pair x y) (Pair a b) =
  let m1 = makeValueMap x a
      m2 = makeValueMap y b
  in Map.union m1 m2

makeValueMap (App x y) (App a b) =
  let m1 = makeValueMap x a
      m2 = makeValueMap y b
  in Map.union m1 m2

makeValueMap c (AppType a b) = makeValueMap c a
makeValueMap c (AppTm a b) = makeValueMap c a
makeValueMap (App x y) (App' a b) = 
  let m1 = makeValueMap x a
      m2 = makeValueMap y b
  in Map.union m1 m2

  
makeValueMap a b = error $ "from makeValueMap: " ++ (show $ disp a <+> text "," <+> disp b)

makeOutput m a@(Star) = a
makeOutput m a@(Const _) = a
makeOutput m (Label l) =
  case Map.lookup l m of
    Nothing -> error "from makeOutput"
    Just i -> fromBool i
    
makeOutput m (Pair x y) =
  Pair (makeOutput m x) (makeOutput m y)
makeOutput m (App x y) = 
  App (makeOutput m x) (makeOutput m y)

runCircuit :: Morphism -> Exp -> Either SimulateError Exp
runCircuit (Morphism minput gs moutput) input =
  let m = makeValueMap minput input
      m' = runState (runExceptT $ runGates gs) m
  in
   case m' of
     (Left e@(AssertionErr _ _ _), _) -> Left $ WrapGates gs e
     (Left e, _) -> Left e
     (Right _, m'') -> Right $ makeOutput m'' moutput
  where runGates gs = mapM_ applyGate gs       

lookupValue :: Variable -> Simulate Bool
lookupValue x =
  do m <- get
     case Map.lookup x m of
       Nothing -> error $ "simulation error: can't find label:" ++ show x
       Just i -> 
         do let m' = Map.delete x m
            put m'
            return i


updateValue :: Variable -> Bool -> Simulate ()
updateValue x v =
  do m <- get
     put $ Map.insert x v m


applyGate :: Gate -> Simulate ()
applyGate (Gate id [] (Label input) (Label output) Star) | getName id == "QNot" = 
  do v <- lookupValue input
     updateValue output (not v)
applyGate (Gate name [] (Pair (Label w) (Label c)) (Pair (Label t) (Label c')) Star) 
  | getName name == "CNot" =
    do wv <- lookupValue w
       cv <- lookupValue c
       updateValue c' cv
       updateValue t (booleanAdd cv wv)

applyGate (Gate name [] Star (Label w) Star) 
  | getName name == "Init0" = updateValue w False

applyGate (Gate name [] Star (Label w) Star) 
  | getName name == "Init1" = updateValue w True

applyGate (Gate name [] (Label w) Star Star) 
  | getName name == "Term0" =
    do w' <- lookupValue w
       if w' then throwError $ AssertionErr w False True
         else return ()

applyGate (Gate name [] (Label w) Star Star) 
  | getName name == "Term1" =
    do w' <- lookupValue w
       if w' then return ()
         else throwError $ AssertionErr w  True False


applyGate (Gate name [v] (Pair (Label w) (Label c)) (Pair (Label t) (Label c')) Star)
  | getName name == "CNotGate" =
    do let v' = toBool v
       wv <- lookupValue w
       cv <- lookupValue c
       updateValue c' cv
       if v' then
         updateValue t (booleanAdd cv wv)
         else updateValue t (booleanAdd (not cv) wv)
         
applyGate (Gate name [v1, v2] (Pair (Pair (Label w) (Label c1)) (Label c2))
           (Pair (Pair (Label t) (Label c1')) (Label c2')) Star)
  | getName name == "ToffoliGate" =
    do let v1' = toBool v1
           v2' = toBool v2
       wvalue <- lookupValue w
       c1value <- lookupValue c1
       c2value <- lookupValue c2
       updateValue c1' c1value
       updateValue c2' c2value
       case (v1', v2') of
         (True, True) -> updateValue t $ (c1value && c2value) `booleanAdd` wvalue
         (True, False) -> updateValue t $ (c1value && not c2value) `booleanAdd` wvalue
         (False, True) -> updateValue t $ (not c1value && c2value) `booleanAdd` wvalue
         (False, False) -> updateValue t $ (not c1value && not c2value) `booleanAdd` wvalue 

applyGate (Gate name [] (Label input) (Label output) ctrl) | getName name == "Not_g"  =
  do let ws = getWires ctrl
     values <- mapM lookupValue ws
     v <- lookupValue input
     if and values then
       do updateValue output (not v)
          mapM_ (\ (x, v) -> updateValue x v) (zip ws values)
          
       else do updateValue output v
               mapM_ (\ (x, v) -> updateValue x v) (zip ws values)
applyGate (Gate name ps input output ctrl) =
  throwError $ NotSupported (getName name)

toBool (Const x) | getName x == "True" = True
toBool (Const x) | getName x == "False" = False
toBool a = error $ show a ++ ":unknown boolean format, bools should be comming from the Prelude module."  

fromBool True = Const (Id "True")
fromBool False = Const (Id "False")

booleanAdd True False = True
booleanAdd True True = False
booleanAdd False True = True
booleanAdd False False = False
