import Mathlib.Algebra.Group.ZeroOne
-- import Batteries.Data.Vector
-- open Batteries

abbrev Vec (n: Nat) (α : Type u) := Vector α n

namespace Vec

/--
  A stream of finite numbers.
  This is useful for iteration over a range of numbers with proof of the invariant.
-/
structure FinRange (n : Nat) where
  curr : Nat
  ok : curr ≤ n

def fins
  (start : Nat)
  (to : Nat)
  (ok : start ≤ to := by omega)
  : FinRange to :=
  { curr := start, ok }

def allFins (n : Nat) : FinRange n := fins 0 n

instance : Stream (FinRange n) (Fin n) where
  next? (fs : FinRange n) : Option (Fin n × FinRange n) :=
    if h : fs.curr < n then
      let i : Fin n := ⟨fs.curr, h⟩
      some (i, { curr := fs.curr + 1, ok := Nat.succ_le_of_lt h })
    else
      none

instance : ToStream (FinRange n) (FinRange n) where
  toStream := id

@[inline]
def empty : Vec 0 α := Vector.mkEmpty 0

/-- Max of a vector. Returns a default value if the vector is empty.-/
def max [Max α] [Inhabited α] (v: Vec n α) : α  :=
  v.foldl (fun max' i => Max.max max' i) v[0]!

/-- Replicate a value n times. -/
@[inline]
def replicate (n: Nat) (x: α) : Vec n α := Vector.mkVector n x

@[inline]
def of (a: α) : Vec n α :=
  replicate n a

@[inline]
def ofFn {n: Nat} (f: Fin n → α ) : Vec n α := Vector.ofFn f

/-- Convert an array to a vector. -/
@[inline]
def ofArray (a : Array α) : Vec a.size α := Vector.mk a (by rfl)

/-- Convert a list to a vector. -/
@[inline]
def ofList (l : List α) : Vec l.length α  := Vec.ofArray l.toArray

syntax "!v[" withoutPosition(sepBy(term, ", ")) "]" : term
macro_rules
  | `(!v[ $elems,* ]) => `(Vec.ofList [ $elems,* ])

@[inline]
def singleton (x : α) : Vec 1 α  :=
  Vector.singleton x

/-- prove that i < v.data.size if i < n-/
theorem lt_n_lt_data_size {n :Nat} (v: Vector n α) (i : Fin n)
  : (i < v.data.size)
  := Nat.lt_of_lt_of_eq i.isLt (Eq.symm v.isEq)

/-- prove that i < n if i < v.array.size-/
theorem lt_data_size_lt_n {i n :Nat}  (v: Vector n α) (h: i < v.data.size)
  : (i < n)
  := v.isEq.symm ▸ h

@[inline]
def get (v: Vector n α) (i : Fin n) : α := Vector.get v i

-- instance to get element
instance : GetElem (Vector n α) Nat α (fun _ i => i < n) where
  getElem xs i h := xs.get ⟨i, h⟩

@[inline]
def set (v: Vector n α) (i : Fin n) (a : α) : Vector n α :=
  -- prove that i ≤ v.data.length
  let i := Fin.mk i.val (Nat.lt_of_lt_of_eq i.isLt (Eq.symm v.isEq))
  {
    data := v.data.set i a,
    isEq := Eq.trans (v.data.size_set i a) v.isEq
  }

@[inline]
def foldl {α β: Type u} {n: Nat} (f: β → α → β) (init: β) (v: Vector n α) : β :=
  v.data.foldl f init

@[inline]
def modify (i: Fin n) (f: α → α) (v: Vector n α) : Vector n α :=
  set v i (f (get v i))

@[inline]
def push (v: Vector n α) (a : α) : Vector (n + 1) α :=  {
  data := v.data.push a,
  isEq := Eq.trans (v.data.size_push a) (congrArg Nat.succ v.isEq)
}

@[inline]
def pop {α: Type u} {n : Nat} (v: Vector n α) : Vector  (n - 1) α :=  {
  data := v.data.pop,
  isEq := Eq.trans (v.data.size_pop) (congrArg Nat.pred v.isEq)
}

@[inline]
def truncateTR {α: Type u} {n : Nat} (v: Vector n α) (n': Nat) (h: n' ≤ n): Vector n' α :=
  if h1: n = n' then
    v.proveLen (v.isEq.trans h1)
  else
    have n'_ne_n := (Ne.intro h1).symm
    have n'_lt_n := Nat.lt_of_le_of_ne h (n'_ne_n)
    have n'_succ_le_n := Nat.succ_le_of_lt n'_lt_n
    v.pop.truncateTR n' (Nat.pred_le_pred n'_succ_le_n)

@[inline]
def truncate {α: Type u} {n : Nat} (v: Vector n α) (n': Nat) (h: n' ≤ n): Vector n' α :=
  .ofFn (v[·])

@[csimp]
theorem truncate_eq_truncateTR : @truncate = @truncateTR := by sorry

@[specialize]
def zipWithAux {i n:Nat} (f : a → b → c) (as : Vector n a) (bs : Vector n b) (acc : Vector i c ) (h : i ≤ n) : Vector n c  :=
  if h1: i = n then
    acc.proveLen (acc.isEq.trans h1)
  else
    -- we have to use letI in order to not have to deal with let fns in the proof when we unfold
    letI h2: i < n := Nat.lt_of_le_of_ne h h1
    zipWithAux f as bs (acc.push (f as[i] bs[i])) h2

@[inline]
def zipWith {β : Type u} {γ : Type u} {n: Nat} (f: α → β → γ) (v1: Vector n α) (v2: Vector n β): Vector n γ :=
  zipWithAux f v1 v2 ⟨Array.mkEmpty n, rfl⟩ (by simp)

def zip {β : Type u} {n: Nat} (v1: Vector n α) (v2: Vector n β): Vector n (α × β)  :=
  zipWith (·, ·) v1 v2

@[inline]
def map {β : Type u} {n: Nat} (f: α → β) (v: Vector n α) : Vector n β  := {
  data := v.data.map f,
  isEq := Eq.trans (v.data.size_map f) v.isEq
}

def unzip {α β : Type u} {n: Nat} (v: Vector n (α × β)): Vector n α × Vector n β :=
  let a := v.map Prod.fst
  let b := v.map Prod.snd
  (a, b)


instance : Functor (Vector n ·) where
  map f xs := xs.map f

-- Not a monad or applicative functor because of the fixed length constraint.
instance : Pure (Vector n ·) where
  pure x := Vector.replicate n x


private def mapIdxHelper  (f: (N:Fin n) → α → β) : Nat → α → β :=
  fun i a =>
  if h0: n = 0 then
    -- If n = 0, then Fin n is equivalent to Empty, so this case is impossible
    have h: Fin 0 := sorry -- TODO fixup, maybe rewrite under f binder?
    Fin.elim0 h
  else
    let i' := i % n
    have h1: i' < n := Nat.mod_lt i (Nat.pos_of_ne_zero h0)
    f (Fin.mk i' h1) a

@[inline]
def mapIdx { α β : Type u} {n: Nat} (f: Fin n → α → β) (v: Vector n α) : Vector n β  :=
  -- empty case needs special handling because mod is not defined on 0
  if h0: n = 0 then
    {
      data := Array.mkEmpty 0,
      isEq := by simp [h0]
    }
  else
    have h: n = v.data.size := by simp [v.isEq]
    -- `f` takes a Nat and mods it by n to get a Fin n
    let f' : (Nat → α → β) := fun i a =>
      let i' := i % n
      have h1: i' < n := Nat.mod_lt i (Nat.pos_of_ne_zero h0)
      f (Fin.mk i' h1) a
    {
      data := Array.mapIdx v.data f',
      isEq := by simp [v.isEq]
    }

/--The zero vector-/
def zero [Zero α] {n : Nat} : Vector n α := replicate n 0

/--The all ones vector-/
def one [One α] {n : Nat} : Vector n α := replicate n 1

/-- Negate a vector-/
def neg [Neg α] (v: Vector n α) : Vector n α := v.map (-·)

/-- Add two vectors-/
def add [Add α] (v1: Vector n α) (v2: Vector n α) : Vector n α :=
  zipWith (·+·) v1 v2

def sub [Sub α] {n : Nat} (a b: Vector n α) : Vector n α :=
  zipWith (·-·) a b

def scale [Mul α] {n: Nat} (k: α) (v: Vector n α) : Vector n α :=
  v.map (k * ·)

def hadamard [Mul α] {n: Nat} (a b: Vector n α) : Vector n α :=
  zipWith (·*·) a b

def sum [Add α] [Zero α] {n: Nat} (v: Vector n α) : α :=
  v.foldl (· + ·) 0

def dot [Add α] [Mul α] [Zero α] {n: Nat} (a b: Vector n α) : α :=
  sum (hadamard a b)

/-- Dot product. The ᵥ is for "vector" -/
infix:25 " ⬝ᵥ " => dot
/-- Hadamard product. Elementwise multiplication. -/
infix:25 " ⊙ " => hadamard



#eval 11 = !v[1, 2].dot !v[3, 4]
#eval !v[1, 2] ⊙ !v[3, 4]

/-- Swap rows and columns of a matrix-/
def transpose  (v: Vector R (Vector C α )) : Vector C (Vector R α ) :=
  ofFn fun c =>
    ofFn fun r =>
    v[r][c]

-- TODO weaken to semiring
def matmul [Add α] [Mul α] [Zero α] (a: Vector R (Vector  I α)) (b: Vector I (Vector  C α )) : Vector R (Vector C α )  :=
  let rows := a
  let cols := b.transpose

  ofFn fun r =>
    ofFn fun c =>
      rows[r] ⬝ᵥ cols[c]


-- Some theorems
@[simp]
theorem getElem_data {α: Type u} {n: Nat} (v: Vector n α) (i: Fin n)
  : v[i] = v.data[i]'(lt_n_lt_data_size v i)
  := rfl

@[simp]
theorem getElem_data' {α: Type u} {n: Nat} (v: Vector n α) (i: Nat) (h: i < n)
  : v[i] = v.data[i]'(lt_n_lt_data_size v ⟨i, h⟩)
  := rfl

@[simp]
theorem getElem_eq_get {α: Type u} {n: Nat} (v: Vector n α) (i: Nat) (h: i < n)
  : v[i] = v.get (Fin.mk i h)
  := rfl

@[simp]
theorem mk_data_eq {α: Type u} (data: Array α) (h: data.size = n)
  : (Vector.mk (n := n) data h).data = data
  := rfl

/-- Object permanence??? 😳 -/
@[simp]
theorem get_set_eq {α: Type u} {n: Nat} (v: Vector n α) (i: Fin n) (a: α)
  : Vector.get (Vector.set v i a) i = a
  := Array.get_set_eq v.data ⟨i, lt_n_lt_data_size v i⟩ a

/-- If we construct a vector through ofFn, then each element is the result of the function -/
@[simp]
theorem get_ofFn {n: Nat} (f: Fin n -> α) (i: Fin n)
  : (ofFn f)[i] = f i
  :=
    -- prove that the i < Array.size (Array.ofFn f)
    have i_lt_size_ofFn_data : i.val < Array.size (Array.ofFn f) := lt_n_lt_data_size (ofFn f) i
    -- prove that v.data.get i = f i
    Array.getElem_ofFn f i.val i_lt_size_ofFn_data

/-- If we construct an array through mkArray then each element is the provided value -/
theorem Array_getElem_mk {n: Nat} (a:α) (i: Nat) (h: i < Array.size (Array.mkArray n a))
  : (Array.mkArray n a)[i] = a
  := by
    rw [Array.getElem_eq_getElem_toList]
    simp [Array.toList_mkArray]

/-- If we construct a vector through replicate, then each element is the provided function -/
@[simp]
theorem get_replicate {n: Nat} (a:α) (i: Fin n)
  : (replicate n a)[i] = a
  :=
    -- prove that the i < Array.size (Array.mkArray n a)
    have i_lt_size_mkArray_data : i.val < Array.size (Array.mkArray n a) := lt_n_lt_data_size (replicate n a) i
    -- prove that v.data.get i = f i
    Array_getElem_mk a i.val i_lt_size_mkArray_data

theorem get_truncate {α: Type u} {n : Nat} (v: Vector n α) (n': Nat) (h: n' ≤ n) (i : Fin n')
  : (v.truncate n' h)[i] = v[i]
  := get_ofFn (fun i => v[i]) i

theorem get_map {β : Type u} {n: Nat} (f: α → β) (v: Vector n α) (i: Fin n)
  : (v.map f)[i] = f v[i]
  := Array.getElem_map f v.data i (lt_n_lt_data_size (v.map f) i)


theorem get_mapIdx {β : Type u} {n: Nat} (f: Fin n → α → β) (v: Vector n α) (i: Fin n)
  : (v.mapIdx f)[i] = f i v[i]
  :=
    let f' : Nat -> α -> β := fun i a => mapIdxHelper f i a
    -- have i_lt_mapIdx_data_size : i.val < (v.mapIdx f').data.size := lt_n_lt_data_size (v.mapIdx f) i
    -- v.data.getElem_mapIdx f'  i.val sorry
    sorry

/-- After push, the last element of the array is what we pushed -/
theorem get_push_eq {n: Nat} (v: Vector n α) (a: α)
  : (v.push a)[n] = a
  :=
     -- prove that n < v.push.data.size
     have n_lt_push_data_size
         : n < (v.push a).data.size
         := Nat.lt_of_lt_of_eq (Nat.lt_succ_self n) (v.push a).isEq.symm
     -- prove that (Vector.push v a)[n] = a
     have array_push_v_data_n_eq_a : (Array.push v.data a)[n] = a := by
        simp only [v.isEq.symm]
        exact Array.getElem_push_eq v.data a
     array_push_v_data_n_eq_a


/-- After push, the previous elements are the same -/
theorem get_push_lt {n: Nat} (v: Vector n α) (a: α) (i: Fin n)
  : (v.push a)[i] = v[i]
  :=
    have i_lt_size_data : i.val < v.data.size := lt_n_lt_data_size v i
    Array.getElem_push_lt v.data a i.val i_lt_size_data

theorem replace_index (v: Vector n α) (i j: Nat) (h1: i < n) (h2: j < n) (h3: i = j)
  : v[i] = v[j]
  := by simp only [h3]

theorem get_push' {n: Nat} (v: Vector n α) (a: α) (i: Nat) (h: i < n+1)
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

theorem get_push {n: Nat} (v: Vector n α) (a: α) (i: Fin (n+1))
  : (v.push a)[i] = if h:i < n then v[i]'h else a
  := get_push' v a i.val i.isLt


theorem get_zipWithAux
    (f : α → β → γ) (as : Vector n α) (bs : Vector n β) (acc : Vector i γ) (hin : i ≤ n)
    (hacc : ∀ (j:Fin i), acc[j] = f as[j] bs[j])
    (k: Fin n)
  : (zipWithAux f as bs acc hin)[k] = f as[k] bs[k]
  := by
      unfold zipWithAux
      split
      case isTrue =>
        rename _ => h1
        exact hacc ⟨k.val, (Nat.lt_of_lt_of_eq k.isLt h1.symm)⟩
      case isFalse =>
        rename _ => h1
        have hin_next: i + 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hin h1)
        exact get_zipWithAux
          -- input elements
          f as bs
          -- accumulator
          (acc.push (f as[i] bs[i]))
          -- proof that accumulator length is valid
          (hin_next)
          -- proof that accumulator is correct
          (by
            intro j
            -- we want to prove that (acc.push (f as[i] bs[i]))[j] = f as[j] bs[j]
            -- split into the case where j < i and j = i
            rw [get_push acc (f as[i] bs[i]) j]
            split
            -- case j < i
            case isTrue =>
              rename _ => h2
              -- prove that acc[j] = f as[j] bs[j]
              exact hacc ⟨j.val, h2⟩
            -- case j = i
            case isFalse =>
              rename _ => h2
              -- prove that f as[i] bs[i] = f as[j] bs[j]
              have h3 : j.val = i := Nat.le_antisymm (Nat.le_of_lt_succ j.isLt) (Nat.ge_of_not_lt h2)
              have h3' : j = ⟨i, Nat.lt.base i⟩ := Fin.eq_of_val_eq h3
              rw [h3']
              rfl
          )
          -- index we want to get
          k

/-- proves the absurd if we have an instance of Fin 0-/
theorem Fin_0_absurd (i: Fin 0) : False
  := by
    have i_lt_0 : i.val < 0 := i.isLt
    exact Nat.not_lt_zero i.val i_lt_0

/-- If we construct a vector through zipWith, then the i'th element is f a[i] b[i] -/
@[simp]
theorem get_zipWith {β : Type u} {γ : Type u} {n: Nat} (f: α → β → γ) (v1: Vector n α) (v2: Vector n β) (i: Fin n)
  : (Vector.zipWith f v1 v2)[i] = f v1[i] v2[i]
  := by unfold zipWith
        exact get_zipWithAux
          -- input elements
          f v1 v2
          -- accumulator
          ⟨Array.mkEmpty n, rfl⟩
          -- a proof that i ≤ n
          (by simp)
          -- a proof that for all j < i, acc[j] = f as[j] bs[j]
          -- note that in this case, i = 0, so we don't have to prove anything
          (by intro z; exact False.elim (Fin_0_absurd z))
          -- the index we want to get
          i

@[ext]
theorem ext {α: Type u} {n: Nat} (v1 v2: Vector n α) (h : ∀ (i : Fin n), v1[i] = v2[i]) :
  v1 = v2
  :=
    -- prove that v1.data.size = v2.data.size
    have v1_data_size_eq_v2_data_size := v1.isEq.trans v2.isEq.symm
    -- prove that for all i < v1.data.size, v1.data.get i = v2.data.get i
    have forall_i_hi_v1_i_v2_i
      : ∀ (i : Nat) (h1: i < v1.data.size) (h2: i < v2.data.size), v1.data[i] = v2.data[i]
      := fun i h1 _ => h ⟨i, lt_data_size_lt_n v1 h1⟩
    -- prove that v1.data = v2.data
    have v1_data_eq_v2_data :v1.data = v2.data :=
        Array.ext
            v1.data
            v2.data
            v1_data_size_eq_v2_data_size
            forall_i_hi_v1_i_v2_i

    -- prove that v1 = v2
    have v1_eq_v2: v1 = v2 := by calc
      v1 = ⟨v1.data, v1.isEq⟩ := by rfl
      _ = ⟨v2.data, v2.isEq⟩ := by simp [v1_data_eq_v2_data]
      v2 = v2 := by rfl
    v1_eq_v2


/--Matrix multiplication.-/
instance [Add α] [Mul α] [Zero α] : HMul (Vector R (Vector I α)) (Vector I (Vector C α)) (Vector R (Vector C α)) where
  hMul := matmul

instance : Inhabited (Vector 0 α) where default := empty
instance [Zero α] : Zero (Vector n α) where zero := zero
instance [One α] : One (Vector n α) where one := one
instance [Neg α] : Neg (Vector n α) where neg := neg
instance [Add α] {n: Nat} : Add (Vector n α) where add := add
instance [Sub α] {n: Nat} : Sub (Vector n α) where sub := sub


/--scalar mul-/
instance [Mul α] {n: Nat} : HMul α (Vector n α) (Vector n α) where
  hMul a v := v.map (a * ·)
/-- scalar mul from the right is the same as scalar mul from the left-/
instance [Mul α] {n: Nat} : HMul (Vector n α) α (Vector n α) where
  hMul v a := a * v
/-- scalar div -/
instance [Div α] {n: Nat} : HDiv (Vector n α) α (Vector n α) where
  hDiv v a := v.map (· / a)

/-- Matrix-vector multiplication -/
instance [Add α] [Mul α] [Zero α] {R C: Nat} : HMul (Vector R (Vector C α)) (Vector C α) (Vector R α) where
  hMul m v := ofFn fun r => m[r] ⬝ᵥ v

/-- Test case for 2x2 matrix-vector multiplication -/
def testMatrixVectorMul : IO Unit := do
  let mat : Vector 2 (Vector 2 Float) := !v[!v[1, 2], !v[3, 4]]
  let vec  : Vector 2 Float := !v[5, 6]
  let result := mat * vec
  IO.println s!"Matrix: {mat}"
  IO.println s!"Vector: {vec}"
  IO.println s!"Result: {result}"
  -- Expected result: [17, 39]

#eval testMatrixVectorMul

/-- Append two vectors -/
def append (v1: Vector n α) (v2: Vector m α) : Vector (n+m) α :=
  {
    data := v1.data.append v2.data,
    isEq := by
      simp [Array.size_append, v1.isEq, v2.isEq]
  }

instance : HAppend (Vector n α) (Vector m α) (Vector (n+m) α ) where hAppend := append


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


def stack (vecs: Vector R (Vector C α)) : Vector (R * C) α :=
  if h: R = 0 then
    {
      data := Array.empty,
      isEq := by
        simp [h]
        exact Array.toList_empty
    }
  else
    let first := stack vecs.pop
    let last := vecs[R-1]
    let q := append first last

    {
      data := q.data,
      isEq := by
        simp [q.isEq, Nat.mul_sub_right_distrib]
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
def split {α : Type u} {R C : Nat} (tosplit: Vector (R * C) α) : Vector R (Vector C α) :=
    ofFn fun r =>
      ofFn fun c =>
        tosplit[splitIdx r c]




#eval! do
  -- Test case for stack
  let v1 := !v[1, 2]
  let v2 := !v[3, 4]
  let v3 := !v[5, 6]
  let stacked := !v[v1, v2, v3].stack
  IO.println s!"Stacked vector: {stacked}"
  -- Expected result: [1, 2, 3, 4, 5, 6]

  -- Test case for split
  let tosplit := !v[1, 2, 3, 4, 5, 6]
  let split : Vector 2 (Vector 3 Float) := tosplit.split
  IO.println s!"Split vectors: {split}"
  -- Expected result: [[1, 2, 3], 4], [5, 6]]

def Vector.sum (v: Vector α n) : α := v.foldl (· + ·) 0
def Vector.sum1 (v: Vector α (n+1) ) : α := Id.run do
  let mut acc := v[0]
  for i in [1:n] do
    acc := acc + v[i]
  acc

/-
## kyle ellefson wishlist
- byaes net
  - user defined tabular and continuous distributions
    -
- [x] gradient descent
- [~] linear algebra
- [ ] marginalization (with syntax)

-/

def _root_.Vector.sum [Add α] [Zero α] (v: Vector α n) : α := v.foldl (· + ·) 0
-- TODO use mathlib and a typeclass
def norm (v: Vector  Float n) : Float := v.map (· ^ 2) |>.sum |>.sqrt


def mean [Add α] (v: Vector α n) : α :=
  v.sum / n.toFloat
end Vector


namespace Plot
-- 
end Plot
