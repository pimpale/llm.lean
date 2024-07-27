import LinearAlgebra.Vector
/-- finite difference approximation of the derivative of a function -/
def finiteDiff (f : Vector Float n → Vector Float m) (x : Vector Float n) (ε := 1e-5) : Vector Float m :=
  let dx := x.map (ε * ·)
  (f (x + dx) - f x) * (1 / dx.norm)
