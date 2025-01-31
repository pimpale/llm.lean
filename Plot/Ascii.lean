import Lean
/-!
# ASCII Plotting Library

Basic components for creating terminal-based plots using Lean 4.
-/

/-- Intercalate for *arrays*. -/
def String.intercalate' (s : String) (l : Array String) : String :=
  l.foldl (fun acc x => acc ++ s ++ x) ""

namespace AsciiPlot

/-- Array version of modifyNth for safer in-place updates -/
def _root_.Array.modifyNth (arr : Array α) (i : Nat) (f : α → α) : Array α :=
  if h : i < arr.size then arr.set i (f arr[i]) h else arr

/-- A single data series with its own style -/
structure Series where
  /-- Label for the series in the legend -/
  label : String
  /-- The points to plot as `(x, y)` pairs -/
  points : Array (Float × Float)
  /-- The character used to plot this series -/
  marker : Char := '•'
deriving Inhabited

/-- Configuration for axis labels and ticks -/
structure AxisConfig where
  /-- Label for the x-axis -/
  xLabel : String := ""
  /-- Label for the y-axis -/
  yLabel : String := ""
  /-- Number of tick marks on x-axis -/
  xTicks : Nat := 5
  /-- Number of tick marks on y-axis -/
  yTicks : Nat := 5
  /-- Whether to show numeric values at ticks -/
  showTickValues : Bool := true
deriving Inhabited

structure AsciiPlot where
  /-- The title of the plot -/
  title : String
  /-- The data series to plot -/
  series : Array Series
  /-- The width of the plot -/
  width : Nat := 60
  /-- The height of the plot -/
  height : Nat := 20
  /-- Whether to show the legend -/
  showLegend : Bool := true
  /-- Axis configuration -/
  axisConfig : AxisConfig := {}
deriving Inhabited

/-- The character used for the border -/
def borderChar := '│'
/-- The character used for the axis -/
def axisChar := '─'
/-- The character used for tick marks -/
def tickChar := '+'

/-- Format a float with specified precision -/
def formatFloat (f : Float) (precision : Nat := 2) : String :=
  let s := toString f
  let parts := s.splitOn "."
  match parts with
  | [whole] => whole
  | [whole, frac] =>
    let truncFrac := frac.take precision
    s!"{whole}.{truncFrac}"
  | _ => s

/-- Generate tick values for an axis -/
def generateTicks (min max : Float) (numTicks : Nat) : Array Float :=
  let range := max - min
  let step := range / (numTicks - 1).toFloat
  Array.range numTicks |>.map fun i => min + i.toFloat * step

/-- Custom string centering implementation -/
def centerString (s : String) (width : Nat) : String :=
  let padding := width - s.length
  let leftPad := padding / 2
  let rightPad := padding - leftPad
  " ".pushn ' ' leftPad ++ s ++ " ".pushn ' ' rightPad

/-- Create axis labels with ticks -/
def createAxisLabels (p : AsciiPlot) (minX maxX minY maxY : Float) : String :=
  if p.axisConfig.xTicks = 0 then ""
  else
    let xTicks := generateTicks minX maxX p.axisConfig.xTicks
    let yTicks := generateTicks minY maxY p.axisConfig.yTicks

    -- X-axis labels
    let xLabels := xTicks.map formatFloat |>.map (centerString · 8)
    let xAxis := "\n" ++ " ".pushn ' ' 6 ++ String.intercalate' " " xLabels

    -- X-axis label if provided
    let xAxisLabel :=
      if p.axisConfig.xLabel ≠ "" then
        "\n" ++ " ".pushn ' ' ((p.width + 2 - p.axisConfig.xLabel.length) / 2) ++ p.axisConfig.xLabel
      else ""

    xAxis ++ xAxisLabel

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

/-- Update normalization to handle multiple series -/
def normalizePoints (p : AsciiPlot) : Array (Array (Nat × Nat)) × (Float × Float × Float × Float) :=
  let allPoints := p.series.map (·.points) |>.foldl (· ++ ·) #[]
  let minX := allPoints.map (·.1) |>.min
  let maxX := allPoints.map (·.1) |>.max
  let minY := allPoints.map (·.2) |>.min
  let maxY := allPoints.map (·.2) |>.max

  let xRange := maxX - minX
  let yRange := maxY - minY

  let normalizeSeries (points : Array (Float × Float)) :=
    points.map fun (x, y) =>
      let scaledX :=
        if xRange == 0 then 0.0
        else (x - minX) / xRange * p.width.toFloat
      let scaledY :=
        if yRange == 0 then 0.0
        else (y - minY) / yRange * p.height.toFloat

      let clampedX := clamp scaledX 0.0 (p.width.toFloat - 1)
      let clampedY := clamp scaledY 0.0 (p.height.toFloat - 1)

      (clampedX.toUInt64.toNat, p.height - clampedY.toUInt64.toNat - 1)

  (p.series.map (·.points) |>.map normalizeSeries, (minX, maxX, minY, maxY))

/-- Create empty grid with borders and axes using Arrays -/
def createGrid (p : AsciiPlot) : Array (Array Char) :=
  let emptyRow := Array.mkArray (p.width + 2) ' '
  let borderRow := #['+'] ++ Array.mkArray p.width axisChar ++ #['+']
  let emptyGrid := Array.mkArray (p.height + 2) emptyRow

  let withTopBorder := emptyGrid.modifyNth 0 (fun _ => borderRow)
  let withBottomBorder := withTopBorder.modifyNth (p.height + 1) (fun _ => borderRow)

  let withLeftBorder := withBottomBorder.map fun row => row.modifyNth 0 (fun _ => borderChar)
  let withAllBorders := withLeftBorder.map fun row => row.modifyNth (p.width + 1) (fun _ => borderChar)

  -- Add tick marks if configured
  let withTicks := if p.axisConfig.xTicks > 0 then
    let tickPositions := Array.range p.axisConfig.xTicks |>.map fun i =>
      (i.toFloat * (p.width.toFloat - 1) / (p.axisConfig.xTicks - 1).toFloat).toUInt64.toNat + 1
    tickPositions.foldl (fun grid pos =>
      grid.modifyNth (p.height + 1) (fun row => row.modifyNth pos (fun _ => tickChar)))
      withAllBorders
  else withAllBorders

  withTicks

/-- Create legend string -/
def createLegend (p : AsciiPlot) : String :=
  if !p.showLegend || p.series.isEmpty then ""
  else
    let legendItems := p.series.map fun s =>
      s!"{s.marker} {s.label}"
    "\nLegend:\n" ++ String.intercalate' "\n" legendItems

/-- Render plot to string -/
def render (p : AsciiPlot) : String :=
  let (normalizedSeries, (minX, maxX, minY, maxY)) := normalizePoints p
  let grid := createGrid p

  -- Add points from each series with its marker
  let gridWithPoints := p.series.zip normalizedSeries |>.foldl
    (fun acc (series, points) =>
      points.foldl (fun grid (x, y) =>
        grid.modifyNth y (fun row => row.modifyNth (x + 1) (fun _ => series.marker)))
        acc)
    grid

  let titleLine := " " ++ centerString p.title (p.width + 2) ++ " \n"
  let legend := createLegend p
  let axisLabels := createAxisLabels p minX maxX minY maxY

  titleLine ++ String.intercalate' "\n" (gridWithPoints.map fun row => String.mk row.toList) ++ axisLabels ++ legend

/-- Automatic string conversion for plots -/
instance : ToString AsciiPlot where
  toString := render

end AsciiPlot

-- Example visualizations
section Examples
open AsciiPlot

/-- Plot multiple trigonometric functions with axis labels -/
def trigPlot : AsciiPlot := {
  title := "Trigonometric Functions",
  series := #[
    { label := "sin(x)",
      points := Array.range 100 |>.map fun x =>
        let x := x.toFloat / 10
        (x, Float.sin x),
      marker := '●' },
    { label := "cos(x)",
      points := Array.range 100 |>.map fun x =>
        let x := x.toFloat / 10
        (x, Float.cos x),
      marker := '○' }
  ],
  width := 60,
  height := 20,
  axisConfig := {
    xLabel := "x",
    yLabel := "y",
    xTicks := 6,
    yTicks := 5,
    showTickValues := true
  }
}

/-- Compare linear and quadratic functions with axis labels -/
def compareLinQuad : AsciiPlot := {
  title := "Linear vs Quadratic",
  series := #[
    { label := "y = x",
      points := Array.range 50 |>.map fun x =>
        let x := x.toFloat / 5 - 5
        (x, x),
      marker := '+' },
    { label := "y = x²",
      points := Array.range 50 |>.map fun x =>
        let x := x.toFloat / 5 - 5
        (x, x^2),
      marker := '*' }
  ],
  width := 50,
  height := 20,
  axisConfig := {
    xLabel := "x",
    yLabel := "f(x)",
    xTicks := 5,
    yTicks := 4,
    showTickValues := true
  }
}

#eval! trigPlot
#eval! compareLinQuad

end Examples
