-- | This module simulates the classical boolean circuits, i.e., circuits
-- that consist of {CNot, QNot, Init0, Init1, Term0, Term1, CNotGate,
-- ToffoliGate, Not_g} from the "lib/Gates.dpq".

module Simulation (runCircuit, SimulateError) where

import SyntacticOperations hiding (toBool)
import Syntax
import Utils


import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.State
import Control.Monad.Except
import Text.PrettyPrint

import Debug.Trace

-- | The boolean simulation monad. It maintains a global state
-- that tracks the boolean values for labels. 
type Simulate a = ExceptT SimulateError (State (Map Label Bool)) a

-- | Apply a circuit to a given value, return the result.
runCircuit :: Morphism -> Value -> Either SimulateError Value
runCircuit (Morphism minput gs moutput) input =
  let m = makeValueMap minput input
      m' = runState (runExceptT $ runGates gs) m
  in
   case m' of
     (Left e@(AssertionErr _ _ _), _) -> Left $ WrapGates gs e
     (Left e, _) -> Left e
     (Right _, m'') -> Right $ makeOutput m'' moutput
  where runGates gs = mapM_ applyGate gs       
        -- Construct a map of values from a template and a boolean value term. 
        makeValueMap :: Value -> Value -> Map Label Bool
        makeValueMap VStar VStar = Map.empty
        makeValueMap (VConst x) (VConst y) | x == y = Map.empty
        makeValueMap (VLabel l) a@(VConst x) =
          Map.fromList [(l, toBool a)]
        makeValueMap (VPair x y) (VPair a b) =
          let m1 = makeValueMap x a
              m2 = makeValueMap y b
          in Map.union m1 m2
        makeValueMap (VApp x y) (VApp a b) =
          let m1 = makeValueMap x a
              m2 = makeValueMap y b
          in Map.union m1 m2
        makeValueMap a b =
          error $ "from makeValueMap: " ++ (show $ disp a <+> text "," <+> disp b)
        -- substitute the labels for values in a given template. 
        makeOutput m a@(VStar) = a
        makeOutput m a@(VConst _) = a
        makeOutput m (VLabel l) =
          case Map.lookup l m of
            Nothing -> error "from makeOutput"
            Just i -> fromBool i
        makeOutput m (VPair x y) =
          VPair (makeOutput m x) (makeOutput m y)
        makeOutput m (VApp x y) = 
          VApp (makeOutput m x) (makeOutput m y)

-- | Simulation error data type.
data SimulateError =
  NotSupported String
  | AssertionErr Label Bool Bool
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

-- | Convert a boolean data type to type 'Bool'.
toBool :: Value -> Bool
toBool (VConst x) | getName x == "True" = True
toBool (VConst x) | getName x == "False" = False
toBool _ = error "unknown boolean format, bools should be coming from the Prelude module"  



-- | Look up a value for a label. Since a label is used linearly,
-- it will be garbage collected once the lookup is done.
lookupValue :: Label -> Simulate Bool
lookupValue x =
  do m <- get
     case Map.lookup x m of
       Nothing -> error $ "simulation error: can't find label:" ++ show x
       Just i -> 
         do let m' = Map.delete x m
            put m'
            return i

-- | Update the boolean value for a label.
updateValue :: Label -> Bool -> Simulate ()
updateValue x v =
  do m <- get
     put $ Map.insert x v m


-- | Update the current state according to the meaning of the
-- gate. The termination of a wired will invoke a runtime check.
applyGate :: Gate -> Simulate ()
applyGate (Gate id [] (VLabel input) (VLabel output) VStar) | getName id == "QNot" = 
  do v <- lookupValue input
     updateValue output (not v)
applyGate (Gate name [] (VPair (VLabel w) (VLabel c)) (VPair (VLabel t) (VLabel c')) VStar) 
  | getName name == "CNot" =
    do wv <- lookupValue w
       cv <- lookupValue c
       updateValue c' cv
       updateValue t (booleanAdd cv wv)

applyGate (Gate name [] VStar (VLabel w) VStar) 
  | getName name == "Init0" = updateValue w False

applyGate (Gate name [] VStar (VLabel w) VStar) 
  | getName name == "Init1" = updateValue w True

applyGate (Gate name [] (VLabel w) VStar VStar) 
  | getName name == "Term0" =
    do w' <- lookupValue w
       if w' then throwError $ AssertionErr w False True
         else return ()

applyGate (Gate name [] (VLabel w) VStar VStar) 
  | getName name == "Term1" =
    do w' <- lookupValue w
       if w' then return ()
         else throwError $ AssertionErr w  True False


applyGate (Gate name [v] (VPair (VLabel w) (VLabel c)) (VPair (VLabel t) (VLabel c')) VStar)
  | getName name == "CNotGate" =
    do let v' = toBool v
       wv <- lookupValue w
       cv <- lookupValue c
       updateValue c' cv
       if v' then
         updateValue t (booleanAdd cv wv)
         else updateValue t (booleanAdd (not cv) wv)
         
applyGate (Gate name [v1, v2] (VPair (VPair (VLabel w) (VLabel c1)) (VLabel c2))
           (VPair (VPair (VLabel t) (VLabel c1')) (VLabel c2')) VStar)
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

applyGate (Gate name [] (VLabel input) (VLabel output) ctrl) | getName name == "Not_g"  =
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

-- | Convert 'Bool' to a boolean data type.
fromBool :: Bool -> Value
fromBool True = VConst (Id "True")
fromBool False = VConst (Id "False")

-- | Add two booleans.
booleanAdd :: Bool -> Bool -> Bool
booleanAdd True False = True
booleanAdd True True = False
booleanAdd False True = True
booleanAdd False False = False
