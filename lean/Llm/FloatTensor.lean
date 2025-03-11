
instance [Zero α] : Zero (Vector α n) := ⟨Vector.mkVector n 0⟩

instance [Add α] : Add (Vector α n) := ⟨Vector.zipWith (· + ·)⟩
instance [Sub α] : Sub (Vector α n) := ⟨Vector.zipWith (· - ·)⟩
instance [Mul α] : Mul (Vector α n) := ⟨Vector.zipWith (· * ·)⟩
instance [Div α] : Div (Vector α n) := ⟨Vector.zipWith (· / ·)⟩

-- scalar addition
instance [Add α] : HAdd (Vector α n) α (Vector α n) := ⟨fun v a => v.map (· + a)⟩
-- scalar subtraction
instance [Sub α] : HSub (Vector α n) α (Vector α n) := ⟨fun v a => v.map (· - a)⟩
-- scalar multiplication
instance [Mul α] : HMul α (Vector α n) (Vector α n) := ⟨fun a v => v.map (· * a)⟩
-- scalar division
instance [Div α] : HDiv (Vector α n) α (Vector α n) := ⟨fun v a => v.map (· / a)⟩


def transpose (a: Vector (Vector α N) M): Vector (Vector α M) N :=
  Vector.ofFn (fun i =>
    Vector.ofFn (fun j =>
      a[j][i]
    )
  )

def norm (a: Vector Float n) : Float :=
  (a * a).sum.sqrt

def normalize (a: Vector Float n) : Vector Float n :=
  a / norm a
