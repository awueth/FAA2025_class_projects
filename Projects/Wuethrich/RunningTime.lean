import Projects.Wuethrich.API
import Projects.Wuethrich.Aux

variable {n p : ℕ} [Fact p.Prime] (xs : Vector (ZMod p) (2 ^ n))

def Vector.fntt_auxT {n : ℕ} (xs : Vector (ZMod p) (2 ^ n)) (ω : ZMod p)
    (powers : Vector (ZMod p) (2 ^ n)) : TimeM (Vector (ZMod p) (2 ^ n)) :=
  match n with
  | 0 => pure xs
  | n + 1 => do
    let powers' := powers.restrictEven -- Assume this is free
    let ws := Vector.cast (Nat.min_eq_left (Nat.pow_le_pow_of_le one_lt_two (Nat.le_add_right n 1))) (powers.take (2 ^ n)) -- Assume this is free

    let y_even ← xs.restrictEven.fntt_auxT (ω ^ 2) powers'
    let y_odd  ← xs.restrictOdd.fntt_auxT (ω ^ 2) powers'

    let left := Vector.zipWith3 (fun e o w ↦ e + w * o) y_even y_odd ws -- Costs O(2 ^ n)
    let right := Vector.zipWith3 (fun e o w ↦ e - w * o) y_even y_odd ws -- Costs O(2 ^ n)

    let result := (Vector.cast (Eq.symm (Nat.two_pow_succ n)) (left ++ right))
    ✓ result, (2 ^ (n + 1))

def Vector.fntt_auxT_time (ω : ZMod p) (powers : Vector (ZMod p) (2 ^ n)) :
    (xs.fntt_auxT ω powers).time = n * 2 ^ n := by
  induction n generalizing ω with
  | zero => simp [Vector.fntt_auxT]
  | succ n ih =>
    unfold Vector.fntt_auxT
    simp only [bind, TimeM.tick, take_eq_extract, TimeM.time_of_bind]
    rw [ih, ih]
    ring
