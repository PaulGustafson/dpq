-- | A circuit displaying module. It is adapted from Quipper. This
-- module is independent from the rest of the dpq modules. In other
-- words, it just gives a different view on the circuit model.

module Printcircuits (printCirc, printCirc_fd) where

import Syntax
import SyntacticOperations
import Utils
import Nominal
import Evaluation


import Text.Printf
import Graphics.EasyRender
import System.IO
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List as List
import Data.Set (Set)
import qualified Data.Set as S





-- | The color white.
white :: Color
white = Color_Gray 1.0

-- | The color black.
black :: Color
black = Color_Gray 0.0

-- ----------------------------------------------------------------------
-- * Style parameters

-- | A data type that holds all the customizable parameters.
data FormatStyle = FormatStyle {
  -- | The RenderFormat to use.
  renderformat :: RenderFormat,
  -- | The color of the background.
  backgroundcolor :: Color,
  -- | The color of the foreground (e.g. wires and gates).
  foregroundcolor :: Color,
  -- | Line width.
  linewidth :: Double,
  -- | Gap for double line representing classical bit.
  coffs :: Double,
  -- | Radius of dots for \"controlled\" gates.
  dotradius :: Double,
  -- | Radius of oplus for \"not\" gate.
  oplusradius :: Double,
  -- | Horizontal column width.
  xoff :: Double,
  -- | Difference between width of box and width of label.
  gatepad :: Double,
  -- | Height of labelled box.
  gateheight :: Double,
  -- | Width and height of \"cross\" for swap gate.
  crossradius :: Double,
  -- | Vertical shift for text labels.
  stringbase :: Double,
  -- | Width of \"bar\" bar.
  barwidth :: Double,
  -- | Height of \"bar\" bar.
  barheight :: Double,
  -- | Width of \"D\" symbol.
  dwidth :: Double,
  -- | Height of \"D\" symbol.
  dheight :: Double,
  -- | Maximal width of a gate label.
  maxgatelabelwidth :: Double,
  -- | Maximal width of a wire label.
  maxlabelwidth :: Double,
  -- | Maximal width of a wire number.
  maxnumberwidth :: Double,
  -- | Font to use for labels on gates.
  gatefont :: Font,
  -- | Font to use for comments.
  commentfont :: Font,
  -- | Color to use for comments.
  commentcolor :: Color,
  -- | Font to use for labels.
  labelfont :: Font,
  -- | Color to use for labels.
  labelcolor :: Color,
  -- | Font to use for numbers.
  numberfont :: Font,
  -- | Color to use for numbers.
  numbercolor :: Color,
  -- | Whether to label each subroutine call with shape parameters
  subroutineshape :: Bool
} deriving Show

-- | A 'FormatStyle' consisting of some default parameters, along with
-- the given 'RenderFormat'.
defaultStyle :: RenderFormat -> FormatStyle
defaultStyle rf = FormatStyle {
  renderformat = rf,
  backgroundcolor = white,
  foregroundcolor = black,
  linewidth = 0.02,
  coffs = 0.03,
  dotradius  = 0.15,
  oplusradius = 0.25,
  xoff = 1.5,
  gatepad = 0.3,
  gateheight  = 0.8,
  crossradius = 0.2,
  stringbase = 0.25,
  barwidth = 0.1,
  barheight = 0.5,
  dwidth = 0.3,
  dheight = 0.4,
  maxgatelabelwidth = 1.1,
  maxlabelwidth = 0.7,
  maxnumberwidth = 0.7,
  gatefont = Font TimesRoman 0.5,
  commentfont = Font TimesRoman 0.3,
  commentcolor = Color_RGB 1 0.2 0.2,
  labelfont = Font TimesRoman 0.3,
  labelcolor = Color_RGB 0 0 1,
  numberfont = Font Helvetica 0.5,
  numbercolor = Color_RGB 0 0.7 0,
  subroutineshape = True
}

-- | The default PDF Style.
pdf :: FormatStyle
pdf = defaultStyle Format_PDF

-- | The default style for encapsulated PostScript output.
eps :: FormatStyle
eps = defaultStyle (Format_EPS 1)

-- | The default style for PostScript output.
ps :: FormatStyle
ps = defaultStyle (Format_PS)

-- ----------------------------------------------------------------------
-- * Signed types

-- | Equip any type with a sign. 'True' means positive and 'False'
-- means negative.
--
-- When used with wires in a circuit, a positive sign is used to
-- represent a positive control, i.e., a filled dot, and a negative
-- sign is used to represent a negative control, i.e., an empty dot.
data Signed a = Signed a Bool
                   deriving (Show)

-- | Add a positive sign to an item.
positive :: a -> Signed a
positive x = Signed x True

-- | Add a negative sign to an item.
negative :: a -> Signed a
negative x = Signed x False

-- | Extract the underlying item of a signed item.
from_signed :: Signed a -> a
from_signed (Signed a b) = a

-- | Extract the sign of a signed item: 'True' is positive, and
-- 'False' is negative.
get_sign :: Signed a -> Bool
get_sign (Signed a b) = b

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- | An unsafe version of 'Map.lookup'. This should only be used for
-- keys that are guaranteed to be in the map. It is an error to call
-- this function otherwise.

mapLookup :: (Ord a, Disp a) => Map a b -> a -> b
mapLookup ds x = case Map.lookup x ds of
                      Nothing -> error $ "can't find " ++ show (disp x)
                      Just v -> v

-- ----------------------------------------------------------------------
-- * Wires and controls

-- | A wire in a circuit is the same thing as a label in
-- Proto-Quipper.
type Wire = Label

-- | A list of controlled wires, possibly empty.
type Controls = [Signed Wire]

-- ----------------------------------------------------------------------
-- * Low-level drawing functions

-- | @'render_line' x0 y0 x1 y1@: Draw a line from (/x0/, /y0/)
-- to (/x1/, /y1/). In case of a zero-length line, draw nothing.
render_line :: X -> Y -> X -> Y -> Draw ()
render_line x0 y0 x1 y1 | x0 == x1 && y0 == y1 = return ()
render_line x0 y0 x1 y1 = draw_subroutine alt $ do
  moveto x0 y0
  lineto x1 y1
  stroke
  where
    alt = [custom_ps $ printf "%f %f %f %f line\n" x0 y0 x1 y1]

-- | @'render_dot' x y@: Draw a filled control dot at (/x/,/y/).
render_dot :: FormatStyle -> X -> Y -> Draw ()
render_dot fs x y = draw_subroutine alt $ do
  arc x y (dotradius fs) 0 360
  fill (foregroundcolor fs)
  where
    alt = [custom_ps $ printf "%f %f dot\n" x y]

-- | @'render_circle' x y@: Draw an empty control dot at (/x/,/y/).
render_circle :: FormatStyle -> X -> Y -> Draw ()
render_circle fs x y = draw_subroutine alt $ do
  arc x y (dotradius fs) 0 360
  fillstroke (backgroundcolor fs)
  where
    alt = [custom_ps $ printf "%f %f circ\n" x y]

-- | @'render_not' x y@: Draw a \"not\" gate at (/x/,/y/).
render_not :: FormatStyle -> X -> Y -> Draw ()
render_not fs x y = draw_subroutine alt $ do
  arc x y (oplusradius fs) 0 360
  fillstroke (backgroundcolor fs)
  render_line (x-(oplusradius fs)) y (x+(oplusradius fs)) y
  render_line x (y-(oplusradius fs)) x (y+(oplusradius fs))
  where
    alt = [custom_ps $ printf "%f %f oplus\n" x y]

-- | @'render_bar' x y@: Draw an init/term bar at (/x/,/y/).
render_bar :: FormatStyle -> X -> Y -> Draw ()
render_bar fs x y = draw_subroutine alt $ do
  rectangle (x - (barwidth fs)/2) (y - (barheight fs)/2) (barwidth fs) (barheight fs)
  fill (foregroundcolor fs)
  where
    alt = [custom_ps $ printf "%f %f bar\n" x y]

-- | Escape special characters in a string literal.
ps_escape :: String -> String
ps_escape [] = []
ps_escape ('\\' : t) = '\\' : '\\' : ps_escape t
ps_escape ('('  : t) = '\\' : '('  : ps_escape t
ps_escape (')'  : t) = '\\' : ')'  : ps_escape t
ps_escape (h : t)    = h : ps_escape t

-- | @'render_init' name x y@: Draw an \"init\" gate at
-- (/x/,/y/), with state /name/.
render_init :: FormatStyle -> String -> X -> Y -> Draw ()
render_init fs name x y = draw_subroutine alt $ do
  render_bar fs x y
  textbox align_right (gatefont fs) (foregroundcolor fs) (x-(xoff fs)/2+(gatepad fs)/2) y (x-(gatepad fs)/2) y (stringbase fs) name
  where
    alt = [custom_ps $ printf "(%s) %f %f init\n" (ps_escape name) x y]

-- | @'render_term' name x y@: Draw a \"term\" gate at
-- (/x/,/y/), with state /name/.
render_term :: FormatStyle -> String -> X -> Y -> Draw ()
render_term fs name x y = draw_subroutine alt $ do
  render_bar fs x y
  textbox align_left (gatefont fs) (foregroundcolor fs) (x+(gatepad fs)/2) y (x+(xoff fs)/2-(gatepad fs)/2) y (stringbase fs) name
  where
    alt = [custom_ps $ printf "(%s) %f %f term\n" (ps_escape name) x y]

-- | @'render_namedgate' name inv x y@: draw a named box centered at
-- (/x/,/y/). If /inv/ = 'True', append an \"inverse\" symbol to the
-- end of the name.
render_namedgate :: FormatStyle -> String -> X -> Y -> Draw ()
render_namedgate fs name x y = draw_subroutine alt $ do
  rectangle (x-gatewidth/2) (y-(gateheight fs)/2) gatewidth (gateheight fs)
  fillstroke (backgroundcolor fs)
  textbox align_center (gatefont fs) (foregroundcolor fs) (x-labelwidth/2) y (x+labelwidth/2) y (stringbase fs) name

  where
    alt = [custom_ps $ printf "(%s) %f %f gate\n" (ps_escape name) x y]
    w = text_width (gatefont fs) name
    labelwidth = min w (maxgatelabelwidth fs)
    gatewidth = labelwidth + (gatepad fs)

-- | @'render_blankgate' name x y@: draw an empty box centered
-- at (/x/,/y/), big enough to hold /name/.
render_blankgate :: FormatStyle -> String -> X -> Y -> Draw ()
render_blankgate fs name x y = draw_subroutine alt $ do
  rectangle (x-gatewidth/2) (y-(gateheight fs)/2) gatewidth (gateheight fs)
  fillstroke (backgroundcolor fs)
  where
    alt = [custom_ps $ printf "(%s) %f %f box\n" (ps_escape name) x y]
    w = text_width (gatefont fs) name
    labelwidth = min w (maxgatelabelwidth fs)
    gatewidth = labelwidth + (gatepad fs)

-- | @'render_controlwire' /x/ /ys/ /ws/ /c/@:
-- Render the line connecting all the box components and all the
-- control dots of some gate.
--
-- Parameters: /x/ is the current /x/-coordinate, /ys/ is an indexed
-- array of /y/-coordinates, /ws/ is the set of wires for boxes, and
-- /c/ is a list of controls.
render_controlwire :: X -> Map Wire Y -> [Wire] -> Controls -> Draw ()
render_controlwire x ys ws c =
  case ws of
    [] -> return ()
    w:ws -> render_line x y0 x y1
      where
        ymap w = ys `mapLookup` w
        y = ymap w
        cy = map (\(Signed w _) -> ymap w) c
        yy = map (\w -> ymap w) ws
        y0 = foldr min y (cy ++ yy)
        y1 = foldr max y (cy ++ yy)

-- | @'render_controldots' /x/ /ys/ /c/@: Render the control dots for
-- the given controls. These are either black or white, depending on
-- the sign of each control.
render_controldots :: FormatStyle -> X -> Map Wire Y -> Controls -> Draw ()
render_controldots fs x ys c = do
  sequence_ [ renderdot x | x <- c ]
  where
    renderdot (Signed w True) = render_dot fs x (ys `mapLookup` w)
    renderdot (Signed w False) = render_circle fs x (ys `mapLookup` w)

-- | @'render_multi_gate' /x/ /ys/ /name/ /inv/ /wires/@: Render the
-- boxes for an /n/-ary gate of the given /name/, potentially
-- /inv/erted, at the given list of /wires/. The first two arguments
-- are the current /x/-coordinate and an indexed array of
-- /y/-coordinates.
render_multi_gate :: FormatStyle -> X -> Map Wire Y -> String -> [Wire] -> Draw ()
render_multi_gate fs x ys name [w] =
  render_namedgate fs name x (ys `mapLookup` w)
render_multi_gate fs x ys name ws =
  sequence_ [ render_namedgate fs (name ++ " " ++ show i) x (ys `mapLookup` a) | (a,i) <- zip ws [1..] ]

-- | @'render_circgate' name x y@: draw a named oval centered at
-- (/x/,/y/).
render_circgate :: FormatStyle -> String -> X -> Y -> Draw ()
render_circgate fs name x y = draw_subroutine alt $ do
  oval x y (0.5*gatewidth) (0.4*(gateheight fs))
  fillstroke (backgroundcolor fs)
  textbox align_center (gatefont fs) (foregroundcolor fs) (x-labelwidth/2) y (x+labelwidth/2) y (stringbase fs) name
  where
    alt = [custom_ps $ printf "(%s) %f %f circgate\n" (ps_escape name) x y]
    w = text_width (gatefont fs) name
    labelwidth = min w (maxgatelabelwidth fs)
    gatewidth = labelwidth + (gatepad fs)

-- | @'render_multi_named_ctrl' /x/ /ys/ /wires/ /names/@: Render
-- the boxes for multiple generalized controls at the given /wires/,
-- using the given /names/. We take special care of the fact that
-- generalized controls may be used non-linearly.
render_multi_named_ctrl :: FormatStyle -> X -> Map Wire Y -> [Wire] -> [String] -> Draw ()
render_multi_named_ctrl fs x ys ws names =
  sequence_ [ render_circgate fs name x (ys `mapLookup` a) | (a,name) <- Map.toList map ]
  where
    -- Combine the labels for w if w has multiple occurrences.
    map = Map.fromListWith (\x y -> y ++ "," ++ x) (zip ws names)

-- | @'render_multi_genctrl' /x/ /ys/ /wires/@: Render the boxes for
-- multiple (numbered) generalized controls at the given /wires/.
render_multi_genctrl :: FormatStyle -> X -> Map Wire Y -> [Wire] -> Draw ()
render_multi_genctrl fs x ys ws = render_multi_named_ctrl fs x ys ws names
  where
    names = map show [1..]

-- | Render gate /g/ at /x/-coordinate /x/ and /y/-coordinates as
-- given by /ys/, which is a map from wires to
-- /y/-coordinates. Returns a pair (/s/,/t/) of draw actions for
-- background and foreground, respectively.
render_gate :: FormatStyle -> Gate -> X -> Map Wire Y -> Y -> (Draw (), Draw ())
render_gate fs (Gate name [] (VPair (VLabel w) (VLabel c)) output VStar) x ys maxh
  | getName name == "CNot" =
  let ymap w = ys `mapLookup` w
      y = ymap w
      c' = positive c
      s2 = render_controlwire x ys [w, c] [c']
      t2 = render_controldots fs x ys [c']
      t3 = render_not fs x y
  in (s2, t2 >> t3)

render_gate fs (Gate name [v] ws@(VPair (VLabel w) (VLabel c)) output VStar) x ys maxh
  | getName name == "R" || getName name == "R*" =
  let
      r = getName name
      c' = positive c
      s2 = render_controlwire x ys [w, c] [c']
      t2 = render_multi_gate fs x ys (r ++ "("++ show (toNum v) ++")") [w]
      t3 = render_controldots fs x ys [c']
  in (s2, t2 >> t3)

render_gate fs (Gate name [v] ws@(VPair (VLabel w) (VLabel c)) output VStar) x ys maxh
  | getName name == "CNotGate" =
  let ymap w = ys `mapLookup` w
      y = ymap w
      c' = if toBool v then positive c else negative c
      s2 = render_controlwire x ys [w, c] [c']
--      t2 = render_multi_gate fs x ys ("CNotG" ++ "("++ show (toBool v) ++")") [w]
      t2 = render_not fs x y
      t3 = render_controldots fs x ys [c']
  in (s2, t2 >> t3)

render_gate fs (Gate name [] (VLabel w) output VStar) x ys maxh
  | getName name == "QNot" =
  let ymap w = ys `mapLookup` w
      y = ymap w
      t = render_not fs x y
  in (return (), t)

render_gate fs (Gate name [] VStar (VLabel w) VStar) x ys maxh
  | getName name == "Init0" =
  let y = ys `mapLookup` w
      t = (render_init fs "0" x y)
  in (return (), t)

render_gate fs (Gate name [] VStar (VLabel w) VStar) x ys maxh
  | getName name == "Init1" =
  let y = ys `mapLookup` w
      t = (render_init fs "1" x y)
  in (return (), t)

render_gate fs (Gate name [] (VPair (VLabel w) (VLabel c)) output VStar) x ys maxh
  | "C_" `isPrefixOf` (getName name) =
  let
      c' = positive c
      s2 = render_controlwire x ys ([w]++[c]) [c']
      t2 = render_multi_gate fs x ys (getName name) [w]
      t3 = render_controldots fs x ys [c']
  in (s2, t2 >> t3)

render_gate fs (Gate name [v] (VPair (VLabel w) (VLabel c)) output VStar) x ys maxh
  | "C_" `isPrefixOf` (getName name) && isBool v =
  let
      c' = if toBool v then positive c else negative c
      s2 = render_controlwire x ys ([w]++[c]) [c']
      t2 = render_multi_gate fs x ys (getName name) [w]
      t3 = render_controldots fs x ys [c']
  in (s2, t2 >> t3)

render_gate fs (Gate name [v] (VPair (VLabel w) (VLabel c)) outs VStar) x ys maxh
  | getName name == "ControlledExpGate" =
  let ymap w = ys `mapLookup` w
      y = ymap w
      c' = if toBool v then positive c else negative c
      s2 = render_controlwire x ys [w, c] [c']
      t2 = render_namedgate fs "Exp" x y
      t3 = render_controldots fs x ys [c']
  in (s2, t2 >> t3)

render_gate fs (Gate name [v1, v2] (VPair (VPair (VLabel w) (VLabel c1)) (VLabel c2)) outs VStar) x ys maxh
  | getName name == "ToffoliGate" && isBool v1 && isBool v2 =
  let ymap w = ys `mapLookup` w
      y = ymap w
      c1' = if toBool v1 then positive c1 else negative c1
      c2' = if toBool v2 then positive c2 else negative c2
      s2 = render_controlwire x ys [w, c1, c2] [c1', c2']
      t3 = render_controldots fs x ys [c1', c2']
      t4 = render_not fs x y
  in (s2, t3 >> t4)

render_gate fs (Gate name [] (VPair (VPair (VLabel w) (VLabel c1)) (VLabel c2)) outs VStar) x ys maxh
  | getName name == "ToffoliGate_01" =
  let ymap w = ys `mapLookup` w
      y = ymap w
      c1' = negative c1
      c2' = positive c2
      s2 = render_controlwire x ys [w, c1, c2] [c1', c2']
      t3 = render_controldots fs x ys [c1', c2']
      t4 = render_not fs x y
  in (s2, t3 >> t4)

render_gate fs (Gate name [] (VPair (VPair (VLabel w) (VLabel c1)) (VLabel c2)) outs VStar) x ys maxh
  | getName name == "ToffoliGate_10" =
  let ymap w = ys `mapLookup` w
      y = ymap w
      c1' = positive c1
      c2' = negative c2
      s2 = render_controlwire x ys [w, c1, c2] [c1', c2']
      t3 = render_controldots fs x ys [c1', c2']
      t4 = render_not fs x y
  in (s2, t3 >> t4)


render_gate fs (Gate name [] (VLabel w) VStar VStar) x ys maxh
  | getName name == "Term0" =
  let y = ys `mapLookup` w
      t = render_term fs "0" x y
  in (return (), t)

render_gate fs (Gate name [] (VLabel w) VStar VStar) x ys maxh
  | getName name == "Term1" =
  let y = ys `mapLookup` w
      t = render_term fs "1" x y
  in (return (), t)


render_gate fs (Gate name params (VPair (VLabel w) (VLabel c)) output ctrl) x ys maxh
  | "C_" `isPrefixOf` (getName name) =
  let
      c' = positive c
      cs = getWires ctrl
      ctrls = map positive cs
      s2 = render_controlwire x ys ([w]++[c]) (c':ctrls)
      t2 = render_multi_gate fs x ys (getName name) [w]
      t3 = render_controldots fs x ys (c':ctrls)
  in (s2, t2 >> t3)

render_gate fs (Gate name [] input outs ctrl) x ys maxh =
  let ymap w = ys `mapLookup` w
      ws1 = getWires input
      cs = getWires ctrl
      ctrls = map positive cs
      s2 = render_controlwire x ys (ws1++cs) ctrls
      t2 = render_multi_gate fs x ys (getName name) ws1
      t3 = render_controldots fs x ys ctrls
  in (s2, t2 >> t3)



render_gate fs a x ys maxh =
  error $ "printing is not supported for gate:\n" ++ (show $ disp a)

-- | A 'Xarity' is a map assigning a starting /x/-coordinate to each
-- wire id.
type Xarity = Map Wire X

-- | Determine the arity of a gate, i.e., the lists of input and
-- output wires (including controls).
gate_arity :: Gate -> ([Wire], [Wire])
gate_arity (Gate name vs input output ctrl) =
   let ctrls = getWires ctrl in (getWires input ++ ctrls, getWires output ++ ctrls)

-- | Figure out how a gate at coordinate /x/ affects the current 'Xarity'.
-- Return a pair (/term/, /new/), where /term/ is the 'Xarity' of wires
-- terminated by this gate, and /new/ is the outgoing 'Xarity' of this
-- gate.
update_xarity :: Xarity -> Gate -> X -> (Xarity, Xarity)
update_xarity xarity gate x =
  let (win, wout) = gate_arity gate
      safe_lookup xarity w =
        case Map.lookup w xarity of
          Just x -> x
          Nothing -> x

      (win', wout') = (win \\ wout, wout \\ win)
      -- extract terminating wires from xarity
      xarity_term = foldl (\xar w -> Map.insert w (xarity `safe_lookup` w) xar) Map.empty win'
      -- extract continuing wires from xarity
      xarity_cont = foldl (\xar w -> Map.delete w xar) xarity win'
      -- add new wires to xarity_cont
      xarity_new = foldl (\xar w -> Map.insert w x xar) xarity_cont wout'
  in
   (xarity_term, xarity_new)

-- | Render a horizontal wire from /x/-coordinate /oldx/ to /x/, using
-- /t/ as the type and figuring out the /y/-coordinate from /ys/ and
-- /w/. If the parameters are invalid (/w/ not in /ys/), throw an
-- error.
render_typeas :: FormatStyle -> Map Wire Y -> X -> X -> Wire -> Draw ()
render_typeas fs ys oldx x w =
  let y = ys `mapLookup` w in
  render_line oldx y x y

-- | Render a bunch of horizontal wires from their respective starting
-- 'Xarity' to /x/.
render_xarity :: FormatStyle -> Map Wire Y -> Xarity -> X -> Draw ()
render_xarity fs ys xarity x = do
  sequence_ [ render_typeas fs ys oldx x w | (w, oldx) <- Map.toList xarity ]

-- | Return the set of all wires that are used by the gate (including
-- inputs, outputs, and controls). This is only used for detecting
-- whether a gate is unary (i.e., has at most one input and at most
-- one output). Unary gates are treated specially because multiple
-- unary gates can be stacked vertically.
wirelist_of_gate (Gate _ _ input output ctrls) = getWires input `union` getWires output `union` getWires ctrls

-- | Pre-processing: figure out the /x/-column of each gate. Returns            
-- (/n/,/xgs/) where /xgs/ is a list of ('Gate', 'X') pairs, and                
-- /n/ is the rightmost /x/-coordinate of the circuit. Here we start            
-- from /x0/ and use constant step /xoff/ taken from the 'FormatStyle'.         
assign_x_coordinates :: FormatStyle -> [Gate] -> X -> (X, [(Gate, X)])
assign_x_coordinates fs gs x0 =
  let ((x,ws), xgs) = mapAccumL (\ (x, ws) g ->
        let merge = case (g, wirelist_of_gate g) of
              (_, [w]) -> Just w
              (_, _) -> Nothing
        in
        case merge of
          Just w ->
            if not (w `elem` ws) then
              ((x, w:ws), (g, x))
            else
              ((x + (xoff fs), [w]), (g, x + (xoff fs)))
          _ ->
            if ws == [] then
              ((x + (xoff fs), []), (g, x))
            else
              ((x + 2.0 * (xoff fs), []), (g, x + (xoff fs)))
        ) (x0, []) gs
  in
   if ws == [] then
     (x, xgs)
   else
     (x + (xoff fs), xgs)

-- | Render the gates in the circuit. The parameters are: /xarity/:             
-- the 'Xarity' of the currently pending wires. /xgs/: the list of              
-- gates, paired with pre-computed /x/-coordinates. /ys/: a map from            
-- wires to pre-computed /y/-coordinates. /x/: the right-most                   
-- /x/-coordinate where the final wires will be drawn to. /maxh/: the           
-- maximal height of comments.                                                  
render_gates :: FormatStyle -> Xarity -> [(Gate, X)] -> Map Wire Y -> X -> Y -> (Draw (), Draw ())
render_gates fs xarity xgs ys x maxh =
  case xgs of
    [] ->
      let s2 = render_xarity fs ys xarity x
      in (s2, return ())
    (g,newx):gls ->
      let (xarity_term, xarity_new) = update_xarity xarity g newx in
      let s1 = render_xarity fs ys xarity_term newx in
      let (s2, t2) = render_gate fs g newx ys maxh in
      let (sx, tx) = render_gates fs xarity_new gls ys x maxh in
      (s1 >> s2 >> sx, t2 >> tx)

-- | Number a list of wires in increasing order, at the given                   
-- /x/-coordinate. If the boolean argument is 'True', put the numbers           
-- to the right of /x/, else to the left.                                       
render_ordering :: FormatStyle -> X -> Map Wire Y -> Bool -> [Wire] -> Draw ()
render_ordering fs x ys b ws =
  sequence_ [ render_number fs i b x (ys `mapLookup` w) | (w,i) <- numbering ]
  where
    numbering = zip ws [1..]

-- | Render the number at the given point (/x/,/y/). If the boolean             
-- argument is 'True', put the number to the right of /x/, else to the left.    
render_number :: FormatStyle -> Int -> Bool -> X -> Y -> Draw ()
render_number fs i True x y = draw_subroutine alt $ do
  textbox align_left (numberfont fs) (numbercolor fs) (x+0.2) y (x+0.2+(maxnumberwidth fs)) y (stringbase fs) (show i)
  where
    alt = [custom_ps $ printf "(%s) %f %f rnumber\n" (ps_escape (show i)) x y]
render_number fs i False x y = draw_subroutine alt $ do
  textbox align_right (numberfont fs) (numbercolor fs) (x-0.2-(maxnumberwidth fs)) y (x-0.2) y (stringbase fs) (show i)
  where
    alt = [custom_ps $ printf "(%s) %f %f lnumber\n" (ps_escape (show i)) x y]

-- | Compute the set of all gates in a circuit (but do not necessarily
-- delete duplicates).
wirelist :: [Gate] -> [Wire]
wirelist [] = []
wirelist (Gate _ _ input output ctrl : gs) =
 (getWires input) ++ (getWires output) ++ (getWires ctrl) ++ (wirelist gs)

-- | @'page_of_ocircuit' name ocirc@: Render the circuit /ocirc/ on a           
-- single page.                                                                 
--                                                                              
-- The rendering takes place in the following user coordinate system:           
--                                                                              
-- \[image coord.png]                                                           
page_of_ocircuit :: FormatStyle -> Value -> Document ()
page_of_ocircuit fs (Wired bd) =
  open bd $ \ ws (VCircuit (Morphism q1 ocirc q2)) ->
  let sc = 10
      (gs, _) = refresh_gates Map.empty ocirc []
      ws = getWires q1 `List.union` wirelist gs
      raw_height = fromIntegral $ List.length ws
      ys = Map.fromList (zip (reverse ws) [0.0 ..])
      maxh = raw_height + 0.3
      bboxy = sc * (raw_height + 1)
      (raw_width,xgs) = assign_x_coordinates fs gs 0.0
      bboxx = sc * (raw_width + (xoff fs) + 2.0)
      xa1 = map (\t -> (t, -(xoff fs))) (getWires q1)
      (rendered_wires, rendered_gates) =
        render_gates fs (Map.fromList xa1) xgs ys raw_width maxh in
  newpage bboxx bboxy $ do
    scale sc sc
    translate ((xoff fs) + 1) 1
    setlinewidth (linewidth fs)
    rendered_wires
    rendered_gates

-- | Print a circuit to a file path.
printCirc circ s = do
  h <- openFile s WriteMode
  render_file h Format_PDF (page_of_ocircuit pdf circ)
  hClose h

-- | Print a circuit to a file handle.
printCirc_fd circ h = do
  render_file h Format_PDF (page_of_ocircuit pdf circ)

-- | Relabel each gate to ensure the input and output
-- wires have the same label names.  It assumes each gate is regular,
-- i.e., input and output should have the same arity for all the
-- non-terminal and non-initial gates. It tries to re-use the label
-- names once a label is terminated.
refresh_gates m [] s = ([], m)
refresh_gates m (Gate name [] input VStar VStar : gs) s
  | getName name == "Term0" || getName name == "Term1" =
    let newInput = renameTemp input m
        (gs', newMap') = refresh_gates m gs (getWires newInput ++ s)
    in (Gate name [] newInput VStar VStar : gs', newMap')

refresh_gates m (Gate name [] VStar output VStar : gs) []
  | getName name == "Init0" || getName name == "Init1" =
    let (gs', newMap') = refresh_gates m gs []
    in (Gate name [] VStar output VStar : gs', newMap')

refresh_gates m (Gate name [] VStar output VStar : gs) (h:s)
  | getName name == "Init0" || getName name == "Init1" =
    let x:[] = getWires output
        m' = m `Map.union` Map.fromList [(x, h)]
        (gs', newMap') = refresh_gates m' gs s
    in (Gate name [] VStar (VLabel h) VStar : gs', newMap')

refresh_gates m (Gate name vs input output ctrl : gs) s =
  let newInput = renameTemp input m
      newCtrl = renameTemp ctrl m
      outWires = getWires output
      newOutput = newInput
      ins = getWires newInput
      newMap = m `Map.union` Map.fromList (zip outWires ins)
      (gs', newMap') = refresh_gates newMap gs s
  in (Gate name vs newInput newOutput newCtrl : gs', newMap')

-- | Check whether a value is a boolean constant.
isBool (VConst x) | getName x == "True" = True
isBool (VConst x) | getName x == "False" = True
isBool _ = False

-- | Convert a boolean value to 'Bool'. It is an error to call this
-- with a value that is not a boolean constant.
toBool (VConst x) | getName x == "True" = True
toBool (VConst x) | getName x == "False" = False

-- | Convert a value to a natural number. It is an error to call this
-- with a value that is not a Peano number.
toNum (VConst x) | getName x == "Z" = 0
toNum (VApp (VConst s) n) | getName s == "S" =
  toNum n + 1
