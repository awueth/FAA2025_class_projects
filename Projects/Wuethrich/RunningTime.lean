import Projects.Wuethrich.API
import Projects.Wuethrich.Aux
import Projects.Wuethrich.Vector

variable {n p : ℕ} [Fact p.Prime] (xs : Vector (ZMod p) (2 ^ n))

def zipWith3T {δ : Type} {α β γ : Type*} {n : ℕ} (f : α → β → γ → δ)
    (v1 : Vector α n) (v2 : Vector β n) (v3 : Vector γ n) : TimeM (Vector δ n) :=
  ⟨⟨Array.zipWith3 f v1.toArray v2.toArray v3.toArray, by simp⟩, n⟩

def appendT {α : Type} {n : ℕ} (v1 : Vector α (2 ^ n)) (v2 : Vector α (2 ^ n)) : TimeM (Vector α (2 ^ (n + 1))) :=
  ⟨(Vector.cast (Eq.symm (Nat.two_pow_succ n)) (v1 ++ v2)), 2 ^ (n + 1)⟩

def getPowersT_loop {p : ℕ} (ω : ZMod p) (size : ℕ) (arr : Array (ZMod p)) (val : ZMod p) : TimeM (Array (ZMod p)) :=
  if arr.size < size then do
      ✓ ()
      getPowersT_loop ω size (arr.push val) (ω * val)
  else
    pure arr
termination_by size - arr.size

theorem getPowersT_loop_time {p : ℕ} (ω : ZMod p) (size : ℕ) (arr : Array (ZMod p)) (val : ZMod p) :
    (getPowersT_loop ω size arr val).time = size - arr.size := by
  generalize hg : size - arr.size = gap
  induction gap generalizing arr val with
  | zero =>
    unfold getPowersT_loop
    rw [Nat.sub_eq_zero_iff_le] at hg
    simp
    grind
  | succ n ih =>
    unfold getPowersT_loop
    simp [Nat.lt_of_sub_eq_succ hg]
    rw [ih]
    · ring
    · rw [Array.size_push]
      omega

def getPowersT (ω : ZMod p) (n : ℕ) : TimeM (Vector (ZMod p) (2 ^ n)) := do
  let initArray := Array.emptyWithCapacity (2 ^ n)
  let arr ← getPowersT_loop ω (2 ^ n) initArray 1
  pure ⟨arr, sorry⟩

theorem getPowersT_time (ω : ZMod p) (n : ℕ) : (getPowersT ω n).time = 2 ^ n := by simp [getPowersT, getPowersT_loop_time]

def Vector.fnttT (ω : ZMod p) : TimeM (Vector (ZMod p) (2 ^ n)) := do
  let powers ← getPowersT ω n
  fntt_auxT xs ω powers
  where fntt_auxT {n : ℕ} (xs : Vector (ZMod p) (2 ^ n)) (ω : ZMod p)
    (powers : Vector (ZMod p) (2 ^ n)) : TimeM (Vector (ZMod p) (2 ^ n)) :=
  match n with
  | 0 => pure xs
  | n + 1 => do
    let powers' := powers.restrictEven -- Assume this is free
    let ws := Vector.cast (Nat.min_eq_left (Nat.pow_le_pow_of_le one_lt_two (Nat.le_add_right n 1))) (powers.take (2 ^ n)) -- Assume this is free

    let y_even ← fntt_auxT xs.restrictEven (ω ^ 2) powers'
    let y_odd  ← fntt_auxT xs.restrictOdd (ω ^ 2) powers'

    let left ← zipWith3T (fun e o w ↦ e + w * o) y_even y_odd ws
    let right ← zipWith3T (fun e o w ↦ e - w * o) y_even y_odd ws

    appendT left right

lemma Vector.fntt_auxT_time' (ω : ZMod p) (powers : Vector (ZMod p) (2 ^ n)) :
    (fnttT.fntt_auxT xs ω powers).time = n * 2 ^ (n + 1) := by
  induction n generalizing ω with
  | zero => simp [fnttT.fntt_auxT]
  | succ n ih =>
    unfold fnttT.fntt_auxT zipWith3T appendT
    simp [bind, take_eq_extract, TimeM.time_of_bind, ih]
    ring

theorem Vector.fnttT_time (ω : ZMod p)  :
    (xs.fnttT ω).time ≤ (n + 1) * 2 ^ (n + 1) := by
  unfold Vector.fnttT
  simp [getPowersT_time, Vector.fntt_auxT_time']
  ring_nf
  gcongr
  simp
