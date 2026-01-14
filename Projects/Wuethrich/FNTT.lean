import Projects.Wuethrich.NTT
import Projects.Wuethrich.Vector
import Projects.Wuethrich.Convolution

/-!
# Fast Number Theoretic Transform (FNTT) on Vectors

This file defines the Fast Number Theoretic Transform (FNTT) and its inverse (IFNTT) acting on `Vector (ZMod p) (2 ^ n)`, where `p` is a prime number.

## Main definitions

* `Vector.fntt ω`: The Fast NTT on vectors.
* `Vector.ifntt ω`: The inverse Fast NTT on vectors.
* `Vector.fastConvolution ω`: Fast convolution algorithm using FNTT.

## Main theorems

* `Vector.fntt_correct`: The FNTT on vectors correctly computes the NTT.
* `Vector.ifntt_correct`: The IFNTT on vectors correctly computes the inverse NTT.
* `Vector.ifntt_fntt`: The IFNTT is a left inverse of the FNTT.
* `Vector.fntt_ifntt`: The FNTT is a right inverse of the IFNTT.
* `Vector.fntt_convolution`: The FNTT transforms convolution into pointwise multiplication.
* `Vector.convolution_ifntt`: The convolution of IFNTTs equals IFNTT of pointwise product.
* `Vector.fastConvolution_correct`: Correctness of the fast convolution algorithm.

-/

variable {n p : ℕ} [Fact p.Prime]

/-- Recursive definition of the NTT of a tuple evaluated at `k`,
used as an intermediate step in proving FNTT correctness -/
def ntt_rec {n : ℕ} (ω : ZMod p) (x : Fin (2 ^ n) → ZMod p) (k : Fin (2 ^ n)) : ZMod p :=
  match n with
  | 0 => x k
  | n + 1 =>
    let k' := Fin.ofNat (2 ^ n) k
    let y_even := ntt_rec (ω ^ 2) (restrictEven x) k'
    let y_odd  := ntt_rec (ω ^ 2) (restrictOdd x)  k'

    y_even + (ω ^ (k : ℕ)) * y_odd

section ntt_rec_correct

variable {ω : ZMod p} (x : Fin (2 ^ (n + 1)) → ZMod p)

/-- Splitting lemma for the NTT, expressing it in terms of the NTTs of the even and odd parts. -/
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

/-- The recursive definition of the NTT coincides with the standard NTT definition. -/
theorem ntt_rec_eq_ntt (h : IsPrimitiveRoot ω (2 ^ n)) (x : Fin (2 ^ n) → ZMod p) :
    ntt_rec ω x = ntt ω x := by
  funext k
  fun_induction ntt_rec ω x k with
  | case1 ω x i => fin_cases i; simp [ntt]
  | case2 ω n x k k' y_even y_odd ih_even ih_odd =>
    cases n with
    | zero =>
      simp [y_even, y_odd, ntt_rec, restrictEven, restrictOdd, Fin.double, Fin.doubleSucc, ntt, mul_comm]
    | succ n =>
      rw [ntt_split x h, ← ih_even, ← ih_odd]
      all_goals simpa [pow_succ] using h.pow_two_of_even_order (by grind)

end ntt_rec_correct

section vector

variable {n : ℕ} (xs : Vector (ZMod p) (2 ^ n))

/-- Helper function to compute powers of a primitive root of unity, by iteratively multiplying by `ω`. -/
def getPowers_loop {p : ℕ} (ω : ZMod p) (size : ℕ) (arr : Array (ZMod p)) (val : ZMod p) : Array (ZMod p) :=
  if arr.size < size then
      getPowers_loop ω size (arr.push val) (ω * val)
  else
    arr
termination_by size - arr.size

/--
The size of the array returned by `getPowers_loop` is equal to the requested size.
Used to ensure well-definedness of `getPowers`.
-/
lemma getPowers_loop_len {p size : ℕ} (ω : ZMod p) (arr : Array (ZMod p)) (val : ZMod p)
    (h_sz : arr.size ≤ size) :
    (getPowers_loop ω size arr val).size = size := by
  fun_induction getPowers_loop ω size arr val with
  | case1 arr val h ih =>
    apply ih
    rw [Array.size_push]
    exact Nat.succ_le_of_lt h
  | case2 arr val h => exact (eq_of_ge_of_le h_sz (Nat.le_of_not_lt h)).symm

/-- Computes the first `2 ^ n` powers of a primitive root of unity `ω` and stores them in a vector. -/
def getPowers (ω : ZMod p) (n : ℕ) : Vector (ZMod p) (2 ^ n) :=
  let initArray := Array.emptyWithCapacity (2 ^ n)
  ⟨getPowers_loop ω (2 ^ n) initArray 1, getPowers_loop_len ω initArray 1 (by simp [initArray])⟩

theorem getElem_getPowers {ω : ZMod p} {k : ℕ} (hk : k < 2 ^ n) : (getPowers ω n)[k] = ω ^ k := by
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
  simp only [Vector.restrictEven, getElem_getPowers, Vector.getElem_ofFn, Vector.get_eq_getElem]
  ring

/-- Fast Number Theoretic Transform (FNTT) on Vectors -/
def Vector.fntt (ω : ZMod p) : Vector (ZMod p) (2 ^ n) := fntt_aux xs ω (getPowers ω n)
  where fntt_aux {n : ℕ} (xs : Vector (ZMod p) (2 ^ n)) (ω : ZMod p)
    (powers : Vector (ZMod p) (2 ^ n)) : Vector (ZMod p) (2 ^ n) :=
  match n with
  | 0 => xs
  | n + 1 =>
    let powers' := powers.restrictEven
    let ws := (powers.extract 0 (2 ^ n)).cast (Nat.min_eq_left (Nat.pow_le_pow_of_le one_lt_two (n.le_add_right 1)))

    let y_even := fntt_aux xs.restrictEven (ω ^ 2) powers'
    let y_odd  := fntt_aux xs.restrictOdd (ω ^ 2) powers'

    let left := zipWith3 (fun e o w ↦ e + w * o) y_even y_odd ws
    let right := zipWith3 (fun e o w ↦ e - w * o) y_even y_odd ws

    (left ++ right).cast (Eq.symm (Nat.two_pow_succ n))

/-- Inverse Fast Number Theoretic Transform (IFNTT) on Vectors -/
def Vector.ifntt (ω : ZMod p) : Vector (ZMod p) (2 ^ n) :=
  (2 ^ n : ZMod p)⁻¹ • xs.fntt ω⁻¹

variable {ω : ZMod p}

/-- The FNTT coincides with the recursive NTT definition. -/
lemma vector_fntt_eq_ntt_rec (hω : IsPrimitiveRoot ω (2 ^ n)) : ntt_rec ω xs.get = (xs.fntt ω).get  := by
  funext j
  unfold Vector.fntt
  let powers := (Vector.finRange (2 ^ n)).map (fun i ↦ ω ^ i.val)
  fun_induction Vector.fntt.fntt_aux xs ω powers with
  | case1 => rfl
  | case2 ω n xs powers powers' ws y_even y_odd left right ih1 ih2 =>
    simp_rw [ntt_rec, Nat.succ_eq_add_one, Fin.ofNat_eq_cast, Vector.fntt.fntt_aux, Vector.get_cast]
    rw [@Vector.get_eq_getElem, restrictEven_of_vector, restrictOdd_of_vector, ih1 hω.of_pow_two, ih2 hω.of_pow_two]
    simp only [Fin.coe_cast, Vector.getElem_append, Vector.getElem_zipWith3, Vector.getElem_cast]
    split_ifs with h
    · congr <;> simp [getPowers_restrictEven, Fin.natCast_eq_mk h, Vector.extract, getElem_getPowers]
    · rw [sub_eq_add_neg, neg_mul_eq_neg_mul, getPowers_restrictEven]
      congr; swap
      · simp [Vector.extract, getElem_getPowers]
        rw [neg_eq_neg_one_mul]
        nth_rw 1 [← Nat.sub_add_cancel (Nat.le_of_not_lt h), pow_add, mul_comm]
        congr
        exact hω.pow_eq_neg_one
      all_goals
      · simp_rw [Fin.ext_iff, Fin.val_natCast]
        rw [Nat.mod_eq_sub_mod (by omega)]
        apply Nat.mod_eq_of_lt (by omega)

/-- Main Theorem: The FNTT on vectors correctly computes the NTT. -/
theorem Vector.fntt_correct (h : IsPrimitiveRoot ω (2 ^ n)) : (xs.fntt ω).get = ntt ω xs.get :=
  Eq.trans (vector_fntt_eq_ntt_rec xs h).symm (ntt_rec_eq_ntt h xs.get)

/--
The IFNTT computes the inverse NTT on vectors correctly.
Follow directly from the correctness of the FNTT, since we defined the IFNTT in terms of the FNTT.
 -/
theorem Vector.ifntt_correct (h : IsPrimitiveRoot ω (2 ^ n)) : (xs.ifntt ω).get = intt ω xs.get := by
  rw [intt_as_ntt, Vector.ifntt]
  funext i
  simp only [get, Fin.coe_cast, getElem_toArray, getElem_smul, smul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  congr
  rw [← xs.fntt_correct h.inv]
  rfl

theorem Vector.getElem_fntt {i : ℕ} (h : IsPrimitiveRoot ω (2 ^ n)) (hi : i < 2 ^ n) : (xs.fntt ω)[i]'hi = (ntt ω xs.get) ⟨i, hi⟩ := by
  rw [← Vector.fntt_correct xs h]
  rfl

theorem Vector.getElem_ifntt {i : ℕ} (h : IsPrimitiveRoot ω (2 ^ n)) (hi : i < 2 ^ n) : (xs.ifntt ω)[i]'hi = (intt ω xs.get) ⟨i, hi⟩ := by
  rw [← Vector.ifntt_correct xs h]
  rfl

/-- The IFNTT is a left inverse of the FNTT. -/
theorem Vector.ifntt_fntt (h : IsPrimitiveRoot ω (2 ^ n)) (hp : ¬p ∣ 2 ^ n) : (xs.fntt ω).ifntt ω = xs := by
  ext i hi
  rw [(xs.fntt ω).getElem_ifntt h hi, fntt_correct xs h, left_inv hp h]
  rfl

/-- The FNTT is a right inverse of the IFNTT. -/
theorem Vector.fntt_ifntt (h : IsPrimitiveRoot ω (2 ^ n)) (hp : ¬p ∣ 2 ^ n) : (xs.ifntt ω).fntt ω = xs := by
  ext i hi
  rw [(xs.ifntt ω).getElem_fntt h hi, ifntt_correct xs h, right_inv hp h]
  rfl

variable (ys : Vector (ZMod p) (2 ^ n))

/-- Convolution theorem for the FNTT -/
theorem Vector.fntt_convolution (h : IsPrimitiveRoot ω (2 ^ n)) : (xs.convolution ys).fntt ω  = (xs.fntt ω).mul (ys.fntt ω) := by
  ext i hi
  unfold Vector.mul
  simp only [Vector.getElem_fntt _ h, getElem_zipWith, ← ntt_convolution_apply xs.get ys.get h]
  congr
  exact Vector.get_convolution xs ys

/-- Convolution theorem for the IFNTT -/
theorem Vector.convolution_ifntt (h : IsPrimitiveRoot ω (2 ^ n)) (hp : ¬p ∣ 2 ^ n) :
    (xs.ifntt ω).convolution (ys.ifntt ω) = (xs.mul ys).ifntt ω := by
  ext i hi
  simp only [Vector.getElem_ifntt _ h, Vector.getElem_convolution]
  have : (xs.mul ys).get = xs.get * ys.get := by
    ext i
    simp [Vector.mul, @get_eq_getElem]
  rw [this, ← convolution_intt_apply xs.get ys.get h hp ⟨i, hi⟩]
  congr
  · exact ifntt_correct xs h
  · exact ifntt_correct ys h

/-- Fast convolution by computing the FNTTs, multiplying pointwise, and then applying the IFNTT. -/
def Vector.fastConvolution (ω : ZMod p) : Vector (ZMod p) (2 ^ n) :=
  ((xs.fntt ω).mul (ys.fntt ω)).ifntt ω

/-- Correctness of the fast convolution algorithm. -/
theorem Vector.fastConvolution_correct (h : IsPrimitiveRoot ω (2 ^ n)) (hp : ¬p ∣ 2 ^ n) :
    (xs.fastConvolution ys ω) = xs.convolution ys := by
  simp_rw [Vector.fastConvolution, ← Vector.convolution_ifntt _ _ h hp, Vector.ifntt_fntt _ h hp]


end vector
