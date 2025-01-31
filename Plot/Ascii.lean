import Lean
/-!
# ASCII Plotting Library

Basic components for creating terminal-based plots using Lean 4.
-/

/-- Intercalate for *arrays*. -/
def String.intercalate' (s : String) (l : Array String) : String :=
  l.foldl (fun acc x => acc ++ s ++ x) ""

namespace AsciiPlot

structure AsciiPlot where
  /-- The title of the plot -/
  title : String
  /-- The points to plot as `(x, y)` pairs -/
  points : Array (Float × Float)
  /-- The width of the plot -/
  width : Nat := 60
  /-- The height of the plot -/
  height : Nat := 20

/-- The character used for the border -/
def borderChar := '│'
/-- The character used for the axis -/
def axisChar := '─'
/-- The character used for the data -/
def dataChar := '•'


/-- Exploits 1/0 to get positive infinity. -/
def _root_.Float.infinity : Float := 1.0 / 0.0
/-- Custom Float infinity since Lean 4 doesn't have Float.infinity -/
notation "∞" => _root_.Float.infinity
/-- Just on float for now. -/
def _root_.Array.min (a : Array Float) : Float :=
  a.foldl (fun acc x => Min.min acc x) ∞
/--Just on float for now.-/
def _root_.Array.max (a : Array Float) : Float :=
  a.foldl (fun acc x => Max.max acc x) (-∞)

/-- Add clamp helper function -/
def clamp (value min max : Float) : Float :=
  if value < min then min
  else if value > max then max
  else value

/-- Update normalization with safety checks -/
def normalizePoints (plot : AsciiPlot) : Array (Nat × Nat) :=
  let minX := plot.points.map (·.1) |>.min
  let maxX := plot.points.map (·.1) |>.max
  let minY := plot.points.map (·.2) |>.min
  let maxY := plot.points.map (·.2) |>.max

  let xRange := maxX - minX
  let yRange := maxY - minY

  plot.points.map fun (x, y) =>
    let scaledX :=
      if xRange == 0 then 0.0
      else (x - minX) / xRange * plot.width.toFloat
    let scaledY :=
      if yRange == 0 then 0.0
      else (y - minY) / yRange * plot.height.toFloat

    let clampedX := clamp scaledX 0.0 (plot.width.toFloat - 1)
    let clampedY := clamp scaledY 0.0 (plot.height.toFloat - 1)

    (clampedX.toUInt64.toNat, plot.height - clampedY.toUInt64.toNat - 1)

#eval normalizePoints {
  title := "Test Plot",
  points := #[(1.0, 1.0), (2.0, 2.0), (3.0, 3.0)],
  width := 10,
  height := 10
}

/-- Array version of modifyNth for safer in-place updates -/
def _root_.Array.modifyNth (arr : Array α) (i : Nat) (f : α → α) : Array α :=
  if h : i < arr.size then arr.set i (f arr[i]) h else arr

/-- Create empty grid with borders and axes using Arrays -/
def createGrid (plot : AsciiPlot) : Array (Array Char) :=
  let emptyRow := Array.mkArray (plot.width + 2) ' '
  let borderRow := #['+'] ++ Array.mkArray plot.width axisChar ++ #['+']
  let emptyGrid := Array.mkArray (plot.height + 2) emptyRow

  let withTopBorder := emptyGrid.modifyNth 0 (fun _ => borderRow)
  let withBottomBorder := withTopBorder.modifyNth (plot.height + 1) (fun _ => borderRow)

  let withLeftBorder := withBottomBorder.map fun row => row.modifyNth 0 (fun _ => borderChar)
  let withAllBorders := withLeftBorder.map fun row => row.modifyNth (plot.width + 1) (fun _ => borderChar)

  withAllBorders

/-- Custom string centering implementation -/
def centerString (s : String) (width : Nat) : String :=
  let padding := width - s.length
  let leftPad := padding / 2
  let rightPad := padding - leftPad
  " ".pushn ' ' leftPad ++ s ++ " ".pushn ' ' rightPad

/-- Render plot to string -/
def render (plot : AsciiPlot) : String :=
  let normalized := normalizePoints plot
  let grid := createGrid plot

  let gridWithPoints := normalized.foldl (fun acc (x, y) =>
    acc.modifyNth y (fun row => row.modifyNth (x + 1) (fun _ => dataChar)))
    grid

  let titleLine := " " ++ centerString plot.title (plot.width + 2) ++ " \n"

  titleLine ++ String.intercalate' "\n" (gridWithPoints.map fun row => String.mk row.toList)

/-- Automatic string conversion for plots -/
instance : ToString AsciiPlot where
  toString := render

end AsciiPlot

-- Example visualizations
section Examples
open AsciiPlot

/-- Plot a sine wave -/
def sinePlot : AsciiPlot := {
  title := "Sine Wave",
  points := Array.range 100 |>.map fun x =>
    let x := x.toFloat / 10
    (x, Float.sin x),
  width := 60,
  height := 20
}

/-- Plot a linear function -/
def linearPlot : AsciiPlot := {
  title := "Linear Function y = x",
  points := Array.range 50 |>.map fun x =>
    let x := x.toFloat / 5
    (x, x),
  width := 50,
  height := 15
}

/-- Plot a quadratic function -/
def quadraticPlot : AsciiPlot := {
  title := "Quadratic Function y = x²",
  points := Array.range 30 |>.map fun x =>
    let x := x.toFloat / 5 - 3
    (x, x^2),
  width := 40,
  height := 15
}

/-- Empty plot demonstration -/
def emptyPlot : AsciiPlot := {
  title := "Empty Plot",
  points := #[],
  width := 30,
  height := 10
}

/-- Plot a single point -/
def singlePointPlot : AsciiPlot := {
  title := "Single Point",
  points := #[(5.0, 5.0)],
  width := 10,
  height := 5
}

/-- Plot y = x with proper scaling -/
def yEqualsXPlot : AsciiPlot := {
  title := "y = x",
  points := Array.range 10 |>.map fun x =>
    let x := x.toFloat
    (x, x),
  width := 20,
  height := 10
}

-- Evaluate the examples using ToString
#eval sinePlot
#eval linearPlot
#eval quadraticPlot
#eval emptyPlot
#eval singlePointPlot
#eval yEqualsXPlot

end Examples
