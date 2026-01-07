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

theorem ntt'_eq_ntt (h : IsPrimitiveRoot ω (2 ^ n)) (x : Fin (2 ^ n) → ZMod p) :
    ntt' ω x = ntt ω x := by
  funext k
  fun_induction ntt' ω x k with
  | case1 ω x i => fin_cases i; simp [ntt]
  | case2 ω n x k k' y_even y_odd ih_even ih_odd =>
    cases n with
    | zero =>
      simp [y_even, y_odd, ntt', restrictEven, restrictOdd, Fin.double, Fin.doubleSucc, ntt, mul_comm]
    | succ n =>
      rw [ntt_split x h, ← ih_even, ← ih_odd]
      all_goals simpa [pow_succ] using h.pow_two_of_even_order (by grind)

end ntt'_correct

section vector

variable {n : ℕ} (xs : Vector (ZMod p) (2 ^ n))

def Vector.fntt_aux {n : ℕ} (xs : Vector (ZMod p) (2 ^ n)) (ω : ZMod p)
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

def getPowers_loop {p : ℕ} (ω : ZMod p) (size : ℕ) (arr : Array (ZMod p)) (val : ZMod p) : Array (ZMod p) :=
  if arr.size < size then
      getPowers_loop ω size (arr.push val) (ω * val)
  else
    arr
termination_by size - arr.size

lemma getPowers_loop_len {p size : ℕ} (ω : ZMod p) (arr : Array (ZMod p)) (val : ZMod p)
    (h_sz : arr.size ≤ size) :
    (getPowers_loop ω size arr val).size = size := by
  fun_induction getPowers_loop ω size arr val with
  | case1 arr val h ih =>
    apply ih
    rw [Array.size_push]
    exact Nat.succ_le_of_lt h
  | case2 arr val h => exact (eq_of_ge_of_le h_sz (Nat.le_of_not_lt h)).symm

def getPowers (ω : ZMod p) (n : ℕ) : Vector (ZMod p) (2 ^ n) :=
  let initArray := Array.emptyWithCapacity (2 ^ n)
  ⟨getPowers_loop ω (2 ^ n) initArray 1, getPowers_loop_len ω initArray 1 (by simp [initArray])⟩

theorem getPowers_getElem {ω : ZMod p} {k : ℕ} (hk : k < 2 ^ n) : (getPowers ω n)[k] = ω ^ k := by
  unfold getPowers
  simp only [Vector.getElem_mk]

  let arr := Array.emptyWithCapacity (α := ZMod p) (2 ^ n)
  let val := (1 : ZMod p)

  suffices ∀ arr val,
    (h_sz : arr.size ≤ 2 ^ n) →                 -- The array doesn't exceed capacity
    (∀ i (hi : i < arr.size), arr[i] = ω ^ i) → -- Existing elements are correct
    val = ω ^ arr.size →                        -- Current val is the next power
    (getPowers_loop  ω (2 ^ n) arr val)[k]'(by rw [getPowers_loop_len ω arr val h_sz]; exact hk) = ω ^ k
    from this arr val (by simp [arr]) (by simp_all [arr]) (by simp [arr]; rfl)

  intro arr val h_sz h_arr_correct h_val_correct

  fun_induction getPowers_loop  ω (2 ^ n) arr val with
  | case1 arr val h ih =>
    unfold getPowers_loop
    simp [h]
    apply ih
    · rw [Array.size_push]
      omega
    · intro i hi
      rw [Array.getElem_push]
      split_ifs with hi
      · exact h_arr_correct i hi
      · rw [h_val_correct]
        congr
        grind
    · simp [h_val_correct, pow_add]
      ring
  | case2 arr val h =>
    unfold getPowers_loop
    simp only [h, ↓reduceIte]
    apply h_arr_correct

lemma getPowers_restrictEven {ω : ZMod p} : getPowers (ω ^ 2) n = (getPowers ω (n + 1)).restrictEven := by
  ext k hk
  simp only [Vector.restrictEven, getPowers_getElem, Vector.getElem_ofFn, Vector.get_eq_getElem]
  ring


def Vector.fntt (ω : ZMod p) : Vector (ZMod p) (2 ^ n) :=
  xs.fntt_aux ω (getPowers ω n)

def Vector.ifntt (ω : ZMod p) : Vector (ZMod p) (2 ^ n) :=
  (2 ^ n : ZMod p)⁻¹ • xs.fntt ω⁻¹

variable {ω : ZMod p}

theorem vector_fntt_eq_tuple_ntt' (hω : IsPrimitiveRoot ω (2 ^ n)) : ntt' ω xs.get = (xs.fntt ω).get  := by
  funext j
  unfold Vector.fntt
  let powers := (Vector.finRange (2 ^ n)).map (fun i ↦ ω ^ i.val)
  fun_induction xs.fntt_aux ω powers with
  | case1 => rfl
  | case2 ω n xs powers powers' ws y_even y_odd left right ih1 ih2 =>
    simp_rw [ntt', Nat.succ_eq_add_one, Fin.ofNat_eq_cast, Vector.fntt_aux,
      Vector.take_eq_extract, Vector.get_cast]
    rw [@Vector.get_eq_getElem, restrictEven_of_vector, restrictOdd_of_vector, ih1 hω.of_pow_two, ih2 hω.of_pow_two]
    simp_rw [Fin.coe_cast, @Vector.getElem_append, Vector.zipWith3, Vector.get_cast, Vector.getElem_ofFn, Fin.cast_mk]
    split_ifs with h
    · congr <;> simp [getPowers_restrictEven, Fin.natCast_eq_mk h, Vector.extract, getPowers_getElem]
    · rw [sub_eq_add_neg, neg_mul_eq_neg_mul, getPowers_restrictEven]
      congr; swap
      · simp [Vector.extract, getPowers_getElem]
        rw [neg_eq_neg_one_mul]
        nth_rw 1 [← Nat.sub_add_cancel (Nat.le_of_not_lt h), pow_add, mul_comm]
        congr
        exact hω.pow_eq_neg_one
      all_goals
      · simp_rw [Fin.ext_iff, Fin.val_natCast]
        rw [Nat.mod_eq_sub_mod (by omega)]
        apply Nat.mod_eq_of_lt (by omega)

theorem Vector.fntt_correct (hω : IsPrimitiveRoot ω (2 ^ n)) : (xs.fntt ω).get = ntt ω xs.get := by
  rw [← ntt'_eq_ntt hω]
  exact (vector_fntt_eq_tuple_ntt' xs hω).symm

end vector
