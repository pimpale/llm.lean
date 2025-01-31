import Plot.Ascii

def main : IO Unit := do
  let points := List.range 100 |>.map fun x =>
    let x := x.toFloat / 10
    (x, Float.sin x)

  let plot : AsciiPlot.AsciiPlot := {
    title := "Sine Wave",
    points := points,
    width := 60,
    height := 20
  }

  IO.println (AsciiPlot.render plot)
