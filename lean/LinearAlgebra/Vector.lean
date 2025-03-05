
instance [ToString α] : ToString (Vector α n) where
  toString v := s!"#v{v.toArray}"

namespace Vector

/-- A stream of finite numbers.
    This is useful for iteration over a range of numbers with proof of the invariant. -/
structure FinRange (n : Nat) where
  curr : Nat
  ok : curr ≤ n

/-- Create a FinRange from start to end -/
def fins
  (start : Nat)
  (to : Nat)
  (ok : start ≤ to := by omega)
  : FinRange to :=
  { curr := start, ok }

/-- Create a FinRange from 0 to n -/
def allFins (n : Nat) : FinRange n := fins 0 n

/-- Get an element of a vector -/
instance {α : Type u} {n : Nat} : GetElem (Vector  α n) (Fin n) α (fun _ i => i < n) where
  getElem xs i h := xs[i]'(h)

#eval
  -- let i : Fin 2 := ⟨1, by simp⟩
  let i :=1
  let v : Vector Nat 2 := #v[1, 2]
  v[i]

instance {n : Nat} : Stream (FinRange n) (Fin n) where
  next? (fs : FinRange n) : Option (Fin n × FinRange n) :=
    if h : fs.curr < n then
      let i : Fin n := ⟨fs.curr, h⟩
      some (i, { curr := fs.curr + 1, ok := Nat.succ_le_of_lt h })
    else
      none

instance {n : Nat} : ToStream (FinRange n) (FinRange n) where
  toStream := id

@[inline]
def empty : Vector α 0 := Vector.mkEmpty 0

instance : EmptyCollection (Vector α 0) := ⟨empty⟩


/-- Max of a vector. Returns a default value if the vector is empty.-/
def max [Max α] [Inhabited α] (v: Vector α n) : α  :=
  v.foldl (fun max' i => Max.max max' i) v[0]!

/-- Replicate a value n times. -/
@[inline]
def replicate (n: Nat) (x: α) : Vector α n := Vector.mkVector n x

@[inline]
def of (a: α) : Vector α 1 :=
  replicate 1 a


/-- Convert an array to a vector. -/
@[inline]
def ofArray (a : Array α) : Vector α a.size := Vector.mk a (by rfl)

/-- Convert a list to a vector. -/
@[inline]
def ofList (l : List α) : Vector α l.length := Vector.mk l.toArray (by rfl)



/-- prove that i < v.data.size if i < n-/
theorem lt_n_lt_data_size {n :Nat} (v: Vector α n) (i : Fin n)
  : (i < v.toArray.size)
  := by simp only [size_toArray, Fin.is_lt]

/-- prove that i < n if i < v.array.size-/
theorem lt_data_size_lt_n {i n :Nat}  (v: Vector α n) (h: i < v.toArray.size)
  : (i < n)
  := by simp_all only [size_toArray]

-- instance to get element
-- instance : GetElem (Vector  α n) (Fin n) α (fun _ i => i < n) where
--   getElem xs i h := xs.get ⟨i, h⟩


@[inline]
def modify (i: Fin n) (f: α → α) (v: Vector α n) : Vector α n :=
  set v i (f (get v i))


/-- Truncate a vector to a smaller length. -/
@[inline]
def truncate {n : Nat} (v: Vector α n) (n': Nat) (h: n' ≤ n): Vector α n' :=
  ofFn (v[·])



/-- Functor instance for vectors -/
instance : Functor (Vector · n) where
  map f xs := xs.map f

-- Not a monad or applicative functor because of the fixed length constraint.
/--TODO is this lawful pure? should `n` only be 1?-/
instance : Pure (Vector · n) where
  pure x := Vector.replicate n x


/--The zero vector-/
def zero [Zero α] {n : Nat} : Vector α n := replicate n 0

-- /--The all ones vector-/
-- def one [One α] {n : Nat} : Vector α n := replicate n 1

/-- Negate a vector-/
def neg [Neg α] {n : Nat} (v: Vector α n) : Vector α n := v.map (-·)

/-- Add two vectors-/
def add [Add α] {n : Nat} (v1: Vector α n) (v2: Vector α n) : Vector α n :=
  v1.zipWith (·+·) v2

/-- Subtract two vectors-/
def sub [Sub α] {n : Nat} (a b: Vector α n) : Vector α n :=
  a.zipWith (·-·) b

/-- Scale a vector by a scalar -/
def scale [Mul α] {n: Nat} (k: α) (v : Vector α n) : Vector α n :=
  v.map (k * ·)

/-- Hadamard product, elementwise multiplication -/
def hadamard [Mul α] {n : Nat} (a b : Vector α n) : Vector α n :=
  a.zipWith (·*·) b

/-- Sum the elements of a vector -/
def sum [Add α] [Zero α] {n: Nat} (v: Vector α n) : α :=
  v.foldl (·+·) 0

/-- Dot product.-/
def dot [Add α] [Mul α] [Zero α] {n: Nat} (a b: Vector α n) : α :=
  sum (hadamard a b)

/-- Dot product. The ᵥ is for "vector" -/
infix:25 " ⬝ᵥ " => dot
/-- Hadamard product. Elementwise multiplication. -/
infix:25 " ⊙ " => hadamard

#eval #v[1, 2].dot #v[3, 4] = 11
#eval (#v[1, 2] ⊙ #v[3, 4]) = #v[3, 8]

/-- Swap rows and columns of a matrix-/
def transpose  (v: Vector  (Vector α C ) R) : Vector (Vector  α R) C :=
  ofFn fun c =>
    ofFn fun r =>

      v[r][c]

-- TODO weaken to semiring
def matmul [Add α] [Mul α] [Zero α] (a: Vector  (Vector   α I) R) (b: Vector  (Vector   α C ) I) : Vector  (Vector α  C ) R :=
  let rows := a
  let cols := b.transpose

  ofFn fun r =>
    ofFn fun c =>
      rows[r] ⬝ᵥ cols[c]


/-- Prove that the data of a vector is the same as the vector itself -/
@[simp]
theorem mk_data_eq {α: Type u} (data: Array α) (h: data.size = n)
  : (Vector.mk (n := n) data h).toArray = data
  := rfl


/-- If we construct a vector through ofFn, then each element is the result of the function -/
@[simp]
theorem get_ofFn {n: Nat} (f: Fin n → α) (i: Fin n)
  : (ofFn f)[i] = f i
  :=
    -- prove that the i < Array.size (Array.ofFn f)
    have i_lt_size_ofFn_data : i.val < Array.size (Array.ofFn f) := lt_n_lt_data_size (ofFn f) i
    -- prove that v.data.get i = f i
    Array.getElem_ofFn f i.val i_lt_size_ofFn_data

/-- If we construct an array through mkArray then each element is the provided value -/
theorem Array_getElem_mk {n: Nat} (a:α) (i: Nat) (h: i < Array.size (Array.mkArray n a))
  : (Array.mkArray n a)[i] = a
  := by simp only [Array.getElem_mkArray]


/-- If we construct a vector through replicate, then each element is the provided function -/
@[simp]
theorem get_replicate {n: Nat} (a:α) (i: Fin n)
  : (replicate n a)[i] = a
  :=
    -- prove that the i < Array.size (Array.mkArray n a)
    have i_lt_size_mkArray_data : i.val < Array.size (Array.mkArray n a) := lt_n_lt_data_size (replicate n a) i
    -- prove that v.data.get i = f i
    Array_getElem_mk a i.val i_lt_size_mkArray_data

theorem get_truncate {α: Type u} {n : Nat} (v: Vector  α n ) (n': Nat) (h: n' ≤ n) (i : Fin n')
  : (v.truncate n' h)[i] = v[i]
  := get_ofFn (fun i => v[i]) i

theorem get_map {β : Type u} {n: Nat} (f: α → β) (v: Vector  α n) (i: Fin n)
  : (v.map f)[i] = f v[i]
  := Array.getElem_map f v.toArray i (lt_n_lt_data_size (v.map f) i)




/-- After push, the last element of the array is what we pushed -/
theorem get_push_eq {n: Nat} (v: Vector  α n) (a: α)
  : (v.push a)[n] = a
  :=
     -- prove that n < v.push.data.size
     have n_lt_push_data_size
         : n < (v.push a).toArray.size
         := Nat.lt_of_lt_of_eq (Nat.lt_succ_self n) (v.push a).size_toArray.symm
     -- prove that (Vector.push v a)[n] = a
     have array_push_v_data_n_eq_a : (Array.push v.toArray a)[n] = a := by
        simp only [v.size_toArray.symm]
        exact Array.getElem_push_eq v.toArray a
     array_push_v_data_n_eq_a


/-- After push, the previous elements are the same -/
theorem get_push_lt {n: Nat} (v: Vector  α n) (a: α) (i: Fin n)
  : (v.push a)[i] = v[i]
  :=
    have i_lt_size_data : i.val < v.toArray.size := lt_n_lt_data_size v i
    Array.getElem_push_lt v.toArray a i.val i_lt_size_data

theorem replace_index (v: Vector  α n) (i j: Nat) (h1: i < n) (h2: j < n) (h3: i = j)
  : v[i] = v[j]
  := by simp only [h3]

theorem get_push' {n: Nat} (v: Vector  α n) (a: α) (i: Nat) (h: i < n+1)
  : (v.push a)[i]'h = if h1:i < n then v[i]'h1 else a
  := by
    split
    case isTrue =>
      rename _ => h1
      exact get_push_lt v a ⟨i, h1⟩
    case isFalse =>
      rename _ => h1
      have h2: i = n := Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.ge_of_not_lt h1)
      rw [replace_index (push v a) i n h (by simp) h2]
      exact get_push_eq v a

theorem get_push {n: Nat} (v: Vector  α n) (a: α) (i: Fin (n+1))
  : (v.push a)[i] = if h:i < n then v[i]'h else a
  := get_push' v a i.val i.isLt


/--Matrix multiplication.-/
instance [Add α] [Mul α] [Zero α] : HMul (Vector  (Vector  α I) R) (Vector  (Vector  α C) I) (Vector  (Vector  α C) R) where
  hMul := matmul

instance : Inhabited (Vector α 0) where default := empty
instance [Zero α] : Zero (Vector α n) where zero := zero

instance [Neg α] : Neg (Vector α n) where neg := neg
instance [Add α] {n: Nat} : Add (Vector α n) where add := add
instance [Sub α] {n: Nat} : Sub (Vector α n) where sub := sub


/--scalar mul-/
instance [Mul α] {n: Nat} : HMul α (Vector  α n) (Vector  α n) where
  hMul a v := v.map (a * ·)
/-- scalar mul from the right is the same as scalar mul from the left-/
instance [Mul α] {n: Nat} : HMul (Vector  α n) α (Vector  α n) where
  hMul v a := a * v
/-- scalar div -/
instance [Div α] {n: Nat} : HDiv (Vector  α n) α (Vector  α n) where
  hDiv v a := v.map (· / a)

/-- Matrix-vector multiplication -/
instance [Add α] [Mul α] [Zero α] {R C: Nat} : HMul (Vector  (Vector  α C) R) (Vector  α C) (Vector  α R) where
  hMul m v := ofFn fun r => m[r] ⬝ᵥ v

/-- Test case for 2x2 matrix-vector multiplication -/
def testMatrixVectorMul : IO Unit := do
  let mat : Vector (Vector Float _) _ := #v[#v[1, 2], #v[3, 4]]
  let vec  : Vector  Float _ := #v[5, 6]
  let result := mat * vec
  IO.println s!"Matrix: {mat}"
  IO.println s!"Vector: {vec}"
  IO.println s!"Result: {result}"
  -- Expected result: [17, 39]

#eval testMatrixVectorMul


instance : HAppend (Vector  α n) (Vector  α m) (Vector  α (n+m) ) where hAppend := append


def splitIdx (r: Fin R) (c: Fin C): Fin (R * C) :=
  let idx := r * C + c

  let hi := by calc
    idx < r * C + C := by
      apply Nat.add_lt_add_left c.isLt
    _ ≤ R * C := by
      rw [← Nat.succ_mul]
      apply Nat.mul_le_mul_right
      exact r.isLt

  ⟨idx, hi⟩


def stack (vecs: Vector  (Vector  α C) R) : Vector  α (R * C) :=
  if h: R = 0 then
    have h2: R * C = 0 := by simp [h]
    @Vector.mk α (R * C) Array.empty (by simp [h2];rfl)
  else
    let first := stack vecs.pop
    let last := vecs[R-1]
    let q := append first last

    {
      toArray := q.toArray,
      size_toArray := by
        simp [q.size_toArray, Nat.mul_sub_right_distrib]
        apply Nat.sub_add_cancel
        -- we need to show that  m ≤ n * m
        conv =>
          lhs
          rw [← Nat.one_mul C]
        apply Nat.mul_le_mul_right C
        -- we need to show that 1 ≤ n
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
    }

/-- Unstack-/
def split {α : Type u} {R C : Nat} (tosplit: Vector  α (R * C)) : Vector  (Vector  α C) R :=
    ofFn fun r =>
      ofFn fun c =>
        tosplit[splitIdx r c]




#eval! do
  -- Test case for stack
  let v1 := #v[1, 2]
  let v2 := #v[3, 4]
  let v3 := #v[5, 6]
  let stacked := #v[v1, v2, v3].stack
  IO.println s!"Stacked vector: {stacked}"
  -- Expected result: [1, 2, 3, 4, 5, 6]

  -- Test case for split
  let tosplit := #v[1, 2, 3, 4, 5, 6]
  let split : Vector  (Vector  Float 3) 2 := tosplit.split
  IO.println s!"Split vectors: {split}"
  -- Expected result: [[1, 2, 3], 4], [5, 6]]

/-
## kyle ellefson wishlist
- bayesian networks
  - user defined tabular and continuous distributions
    -
- [x] gradient descent
- [~] linear algebra
- [ ] marginalization (with syntax)

-/
/-- p-norm of a vector-/
def norm (v: Vector  Float n) (p : Float := 2) : Float := v.map (·^p) |>.sum |>.sqrt



def mean  (v: Vector Float n) : Float :=
  v.sum / n.toFloat

end Vector

/--Float powers via exponentiation by squaring-/
instance: HPow Float Nat Float where
  hPow x n := Id.run do
    let mut out := 1.0
    let mut b := x
    let mut e := n
    while e > 0 do
      if e % 2 == 1 then
        out := out * b
      b := b * b
      e := e / 2
    out

/-- factorial of a natural number-/
def _root_.Nat.factorial (n: Nat) : Nat :=
  if n = 0 then
    1
  else
    n * Nat.factorial (n - 1)

/-- binomial coefficient (n choose k)-/
def _root_.Nat.choose (n: Nat) (k: Nat) : Nat :=
  if k > n then
    0
  else
    Nat.factorial n / (Nat.factorial k * Nat.factorial (n - k))

/-- Float multiplication via multiplication by doubling (tropical-style exponentiation via squaring)-/
instance: HMul Nat Float Float where
  hMul n x := Id.run do
    let mut acc := 0.0
    let mut n := n
    let mut x := x
    while n > 0 do
      if n % 2 == 1 then
        acc := acc + x
      x := x + x  -- Double x (tropical-style squaring)
      n := n / 2   -- Halve n (bit shift right)
    acc

@[inherit_doc instHMulNatFloat_lean]
instance: HMul Float Nat Float where
  hMul x n := Id.run do
    let mut acc := 0.0
    let mut n := n
    let mut x := x
    while n > 0 do
      if n % 2 == 1 then
        acc := acc + x
      x := x + x
      n := n / 2
    acc


