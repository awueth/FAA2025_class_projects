import Projects.Wuethrich.NTT

variable {n p : ℕ} [Fact p.Prime]

def ntt' {n : ℕ} (ω : ZMod p) (x : Fin (2 ^ n) → ZMod p) (k : Fin (2 ^ n)) : ZMod p :=
  match n with
  | 0 => x k
  | n + 1 =>
    let k' := Fin.ofNat (2 ^ n) k
    let y_even := ntt' (ω ^ 2) (restrictEven x) k'
    let y_odd  := ntt' (ω ^ 2) (restrictOdd x)  k'

    y_even + (ω ^ (k : ℕ)) * y_odd

section ntt'_correct

variable {ω : ZMod p} (x : Fin (2 ^ (n + 1)) → ZMod p)

lemma ntt_split (h : IsPrimitiveRoot ω (2 ^ (n + 1))) (k : Fin (2 ^ (n + 1))) : ntt ω x k =
    ntt (ω ^ 2) (restrictEven x) (Fin.ofNat (2 ^ n) k) +
    (ω ^ k.val) * ntt (ω ^ 2) (restrictOdd x) (Fin.ofNat (2 ^ n) k) := by
  unfold ntt
  rw [sum_even_odd_split, Finset.mul_sum]
  congr <;> (funext j; simp only [Fin.double, Fin.doubleSucc])
  · congr 1
    norm_cast
    simp [mul_right_comm, pow_mul, ← h.pow_two_fin_of_nat]
    ring
  · rw [← mul_assoc, mul_comm (ω ^ k.val), mul_assoc, Nat.cast_add,
     Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Fin.ofNat_eq_cast,
     add_mul, zpow_add₀ (h.ne_zero (NeZero.ne (2 ^ (n + 1)))), one_mul,
     zpow_natCast, mul_comm (ω ^ k.val)]
    congr 2
    norm_cast
    simp [mul_right_comm, pow_mul, ← h.pow_two_fin_of_nat]
    ring

theorem ntt'_eq_ntt (hn0 : n ≠ 0) (h : IsPrimitiveRoot ω (2 ^ n)) (x : Fin (2 ^ n) → ZMod p) :
    ntt' ω x = ntt ω x := by
  funext k
  fun_induction ntt' ω x k with
  | case1 => simp_all
  | case2 ω n x k k' y_even y_odd ih_even ih_odd =>
    cases n with
    | zero =>
      simp [y_even, y_odd, ntt', restrictEven, restrictOdd, Fin.double, Fin.doubleSucc, ntt, mul_comm]
    | succ n =>
      rw [ntt_split x h, ← ih_even (Ne.symm (Nat.zero_ne_add_one n)),
       ← ih_odd (Ne.symm (Nat.zero_ne_add_one n))]
      all_goals simpa [pow_succ] using h.pow_two_of_even_order (by grind)

end ntt'_correct

section vector

def Vector.fntt_aux {n : ℕ} (ω : ZMod p) (xs : Vector (ZMod p) (2 ^ n))
    (powers : Vector (ZMod p) (2 ^ n)) : Vector (ZMod p) (2 ^ n) :=
  match n with
  | 0 => xs
  | n + 1 =>
    let powers' := powers.restrictEven
    let ws := Vector.cast (Nat.min_eq_left (Nat.pow_le_pow_of_le one_lt_two (Nat.le_add_right n 1))) (powers.take (2 ^ n))

    let y_even := xs.restrictEven.fntt_aux (ω ^ 2) powers'
    let y_odd  := xs.restrictOdd.fntt_aux (ω ^ 2) powers'

    let left := Vector.zipWith3 (fun e o w ↦ e + w * o) y_even y_odd ws
    let right := Vector.zipWith3 (fun e o w ↦ e - w * o) y_even y_odd ws

    Vector.cast (Eq.symm (Nat.two_pow_succ n)) (left ++ right)

/-
def getPowers' (ω : ZMod p) (n : ℕ) : Vector (ZMod p) (2 ^ n) :=
  let size := 2 ^ n
  let initArray := Array.emptyWithCapacity size

  let rec loop (arr : Array (ZMod p)) (val : ZMod p) : Array (ZMod p) :=
    if h : arr.size < size then
      let newArr := arr.push val
      loop newArr (ω * val)
    else
      arr
    termination_by size - arr.size

  ⟨loop initArray 1, sorry⟩
-/

def getPowers (ω : ZMod p) (n : ℕ) : Vector (ZMod p) (2 ^ n) :=
  let emptyList := List.replicate (2 ^ n - 1) ()
  let powerList : List (ZMod p) := emptyList.scanl (fun acc _ ↦ acc * ω) 1

  ⟨powerList.toArray, by simp only [List.size_toArray, List.length_scanl, List.length_replicate,
    powerList, emptyList]; exact Nat.sub_add_cancel Nat.one_le_two_pow⟩

/-
instance : Fact (Nat.Prime 23) := by
  rw [@fact_iff]
  exact Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl

#eval! getPowers' (2 : ZMod 23) 2
#eval getPowers (2 : ZMod 23) 2
-/

/-
example {ω : ZMod p} : getPowers (ω ^ 2) n = (getPowers ω (n + 1)).restrictEven := by
  simp [Vector.restrictEven]
  ext k hk
  simp [getPowers]
  fun_induction List.foldl (fun acc x ↦ acc * ω) 1 (List.replicate (min (2 * k) (2 ^ (n + 1) - 1)) ()) with
  | case1 => sorry
  | case2 => sorry
-/



def Vector.fntt {n : ℕ} (ω : ZMod p) (xs : Vector (ZMod p) (2 ^ n)) : Vector (ZMod p) (2 ^ n) :=
  let powers := (Vector.finRange (2 ^ n)).map (fun i ↦ ω ^ i.val) -- Runs in O(2 ^ n), replace iwth getPowers
  xs.fntt_aux ω powers

theorem vector_fntt_eq_tuple_ntt' {n : ℕ} {ω : ZMod p} (xs : Vector (ZMod p) (2 ^ n))
    (hω : IsPrimitiveRoot ω (2 ^ n)) : ntt' ω (fun i => xs.get i) = fun i => (xs.fntt ω).get i := by
  funext j
  unfold Vector.fntt
  let powers := (Vector.finRange (2 ^ n)).map (fun i ↦ ω ^ i.val)
  fun_induction xs.fntt_aux ω powers with
  | case1 => rfl
  | case2 ω n xs powers powers' ws y_even y_odd left right ih1 ih2 =>
    simp only [ntt', Nat.succ_eq_add_one, Fin.ofNat_eq_cast, Vector.fntt_aux,
      Vector.take_eq_extract, Vector.get_cast]
    rw [@Vector.get_eq_getElem, ok_even, ok_odd, ih1 hω.of_pow_two, ih2 hω.of_pow_two]
    simp only [Fin.coe_cast]
    rw [@Vector.getElem_append]
    split_ifs with h
    · simp only [Vector.zipWith3, Vector.get_cast, Vector.getElem_ofFn, Fin.cast_mk]
      congr
      · simp [Vector.restrictEven]
        ext k hk
        simp
        rw [← @pow_mul]
        congr
        simp [Vector.finRange]
      · exact Fin.natCast_eq_mk h
      · simp [Vector.map]
      · simp [Vector.restrictEven]
        ext k hk
        simp
        rw [← @pow_mul]
        congr
        simp [Vector.finRange]
      · exact Fin.natCast_eq_mk h
    · simp only [Vector.zipWith3, Vector.get_cast, Vector.getElem_ofFn, Fin.cast_mk]
      have hcast : @Nat.cast (Fin (2 ^ n)) (Fin.NatCast.instNatCast (2 ^ n)) ↑j
          = ⟨↑j - 2 ^ n, by omega⟩ := by
        rw [@Fin.eq_mk_iff_val_eq]
        simp only [Nat.succ_eq_add_one, Fin.val_natCast]
        rw [@Nat.mod_eq_iff]
        right
        constructor
        · omega
        · use 1
          grind
      rw [sub_eq_add_neg, neg_mul_eq_neg_mul]
      congr
      · simp [Vector.restrictEven]
        ext k hk
        simp
        rw [← @pow_mul]
        congr
        simp [Vector.finRange]
      · simp only [Vector.get_eq_getElem]
        rw [neg_eq_neg_one_mul]
        nth_rw 1 [← Nat.sub_add_cancel (Nat.le_of_not_lt h), pow_add, mul_comm]
        congr
        · exact hω.pow_eq_neg_one
        · simp [Vector.map]
      · simp [Vector.restrictEven]
        ext k hk
        simp
        rw [← @pow_mul]
        congr
        simp [Vector.finRange]

end vector
