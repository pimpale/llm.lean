import Llm.Matmul
import Llm.FloatTensor

set_option diagnostics true

/-- centered finite difference approximation of the derivative of a function -/
def finiteDiff (f : Vector Float n → Vector Float m) (x : Vector Float n) (ε := 1e-6) : Vector Float m :=
  let dx := ε * x

  (f (x + dx) - f (x - dx)) / (2*norm dx)

/-- Coerce a scalar to a vector of length 1 -/
instance : Coe a (Vector a 1) where
  coe a := #v[a]

#eval ((2.0:Float) : Vector Float 1)
#eval finiteDiff (f:=fun x => (Vector.singleton (dot x x) : Vector Float 1)) (x:= #v[1,2,3])

-- Test case for x^2
def square (x: Vector Float n) : Vector Float n := x * x

#eval square (Vector.mkVector 5 2.0)


def test_finiteDiff_square (n : Nat) : Bool := Id.run do
  let x := Vector.mkVector n 2.0 -- Vector of 2.0s
  let df := finiteDiff square x
  let expected := Vector.mkVector n 4.0 -- Derivative of x^2 is 2x, so at x=2, it's 4
  -- dbg_trace df
  -- dbg_trace expected
  -- Check if the finite difference approximation is close to the expected value
  let tolerance := 1e-4
  let isClose := df.zipWith (λ a b => (Float.abs (a - b) < tolerance : Bool)) expected

  isClose.foldl (· && ·) true

def run_test_finiteDiff_square (n : Nat:=1) : IO Unit := do
  let result := test_finiteDiff_square n -- Test with a vector of size 5
  if result then
    IO.println "Test passed: finite difference of x^2 at x=2 is approximately correct"
  else
    IO.println "Test failed: finite difference of x^2 at x=2 is not within tolerance"

#eval run_test_finiteDiff_square 1
