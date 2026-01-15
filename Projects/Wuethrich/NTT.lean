import Mathlib.Algebra.Field.ZMod
import Projects.Wuethrich.Aux
import Projects.Wuethrich.PrimitiveRoots
import Projects.Wuethrich.Convolution

/-!
# Number Theoretic Transform

This file defines the Number Theoretic Transform (NTT) and its inverse (INTT) acting on tuples `Fin n → ZMod p`, where `p` is a prime number.

## Main definitions

* `ntt ω x`: The NTT of `x : Fin n → ZMod p` with respect to the primitive root of unity `ω`.
* `intt ω x`: The inverse NTT of `x : Fin n → ZMod p` with respect to the primitive root of unity `ω`.

## Main theorems

* `left_inv`: The INTT is a left inverse of the NTT, provided that `p` does not divide `n`.
* `right_inv`: The INTT is a right inverse of the NTT, provided that `p` does not divide `n`.
* `ntt_add`: The NTT is additive.
* `ntt_smul`: The NTT is compatible with scalar multiplication.
* `ntt_shift`: Shift property of the NTT relating frequency shifts to modulation in the time domain.
* `ntt_convolution`: The NTT transforms convolution into pointwise multiplication.
* `intt_convolution`: The INTT of a convolution equals scaled pointwise product of INTTs.
* `convolution_ntt`: The convolution of NTTs equals scaled NTT of pointwise product.
* `convolution_intt`: The convolution of INTTs equals INTT of pointwise product.

-/

variable {n p : ℕ} [Fact p.Prime] (ω : ZMod p)

def ntt : (Fin n → ZMod p) → (Fin n → ZMod p) :=
  fun x k ↦ ∑ j, x j * ω ^ ((j * k) : ℤ)

/-- Auxiliary inverse NTT that omits the normalization factor `(n : ZMod p)⁻¹`. -/
def intt_aux : (Fin n → ZMod p) → (Fin n → ZMod p) :=
  fun x k ↦ ∑ j, x j * ω ^ (-(j * k : ℤ))

def intt (x : Fin n → ZMod p) : (Fin n → ZMod p) := (n : ZMod p)⁻¹ • intt_aux ω x

theorem intt_as_ntt (x : Fin n → ZMod p) : intt ω x = (fun _ ↦ (n : ZMod p)⁻¹) * ntt ω⁻¹ x := by
  unfold ntt intt intt_aux
  simp_all only [zpow_neg, inv_zpow']
  rfl

theorem intt_as_ntt' : intt (n := n) ω = (n : ZMod p)⁻¹ • ntt (n := n) ω⁻¹ := by
  unfold ntt intt intt_aux
  simp_all only [zpow_neg, inv_zpow']
  rfl

theorem ntt_add (ω : ZMod p) (x y : Fin n → ZMod p) : ntt ω (x + y) = ntt ω x + ntt ω y := by
  funext k
  simp [ntt, ← Finset.sum_add_distrib]
  group

theorem ntt_smul (ω : ZMod p) (x : Fin n → ZMod p) (a : ZMod p) : ntt ω (a • x) = a • ntt ω x := by
  funext k
  simp [ntt, Finset.mul_sum]
  group

theorem ntt_shift {ω : ZMod p} (x : Fin n → ZMod p) (i j : Fin n) (h : IsPrimitiveRoot ω n)  :
    ntt ω x (i - j) = ntt ω (fun k ↦ ω ^ (-(j : ℤ) * k) * x k) i := by
  unfold ntt
  by_cases h0 : n = 0; subst h0; exact i.elim0
  refine Finset.sum_congr rfl (fun k _ ↦ ?_)
  simp_rw [mul_comm _ (x k), mul_assoc]
  congr
  rw [← zpow_add₀ (h.ne_zero h0)]
  by_cases hij : j ≤ i
  · congr
    norm_cast
    simp [Fin.sub_val_of_le hij, Nat.mul_sub]
    rw [Nat.cast_sub (by gcongr; exact hij)]
    push_cast
    ring
  · rw [@Fin.intCast_val_sub_eq_sub_add_ite]
    simp only [hij, ↓reduceIte]
    rw [mul_add]
    rw [zpow_add₀ (h.ne_zero h0), zpow_mul' ω k n, zpow_natCast ω n, h.pow_eq_one, one_zpow, mul_one]
    congr
    ring

variable {ω : ZMod p}

lemma left_inv_aux (h : IsPrimitiveRoot ω n) (x : Fin n → ZMod p) :
    intt_aux ω (ntt ω x) = n • x := by
  by_cases h₀ : n = 0; subst h₀; funext i; exact i.elim0
  unfold ntt intt_aux
  funext k
  simp_rw [Finset.sum_mul, mul_assoc,
   ← zpow_add' (Or.inl (IsPrimitiveRoot.ne_zero h h₀))]
  conv => left; arg 2; intro j; arg 2; intro l; arg 2; arg 2; ring_nf; rw [mul_comm, ← mul_sub]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, h.sum_zpow_mul_eq]
  simp [cast_divides_helper, mul_comm]

lemma right_inv_aux (h : IsPrimitiveRoot ω n) (x : Fin n → ZMod p) :
    ntt ω (intt_aux ω x) = n • x := by
  by_cases h₀ : n = 0; subst h₀; funext i; exact i.elim0
  unfold ntt intt_aux
  funext k
  simp only [Pi.smul_apply, nsmul_eq_mul]
  calc
    ∑ i : Fin n, (∑ j, x j * ω ^ (-((j : ℤ) * i))) * ω ^ ((i : ℤ) * k) =
      ∑ i : Fin n, ∑ j, x j * ω ^ (-((j : ℤ) * i) + i * k) := by
      simp_rw [Finset.sum_mul, mul_assoc, ← zpow_add' (Or.inl (IsPrimitiveRoot.ne_zero h h₀))];
    _ = ∑ i : Fin n, ∑ j, x j * ω ^ (i * ((k : ℤ) - j)) := by rcongr; ring
    _ = ∑ j, x j * ∑ i : Fin n,  ω ^ (i * ((k : ℤ) - j)) := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ j : Fin n, x j * ↑(if ↑n ∣ (↑k : ℤ) - j then n else 0) := by simp_rw [h.sum_zpow_mul_eq];
    _ = n * x k := by simp [cast_divides_helper, mul_comm]

theorem left_inv (hp : ¬p ∣ n) (h : IsPrimitiveRoot ω n) (x : Fin n → ZMod p) :
    intt ω (ntt ω x) = x := by
  rw [intt, inv_smul_eq_iff₀]
  · simp_all [left_inv_aux h x]
    rfl
  · rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hp

theorem right_inv (hp : ¬p ∣ n) (h : IsPrimitiveRoot ω n) (x : Fin n → ZMod p) :
    ntt ω (intt ω x) = x := by
  rw [intt, ntt_smul, right_inv_aux h x, inv_smul_eq_iff₀]
  · simp_all
    rfl
  · rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hp


section convolution

variable {ω : ZMod p} (x y : Fin n → ZMod p)

theorem ntt_convolution_apply (h : IsPrimitiveRoot ω n) (k : Fin n) : ntt ω (x ⋆ y) k = (ntt ω x) k * (ntt ω y) k:= by
  conv_lhs => simp only [Pi.mul_apply, ntt, convolution, Finset.sum_mul]; rw [Finset.sum_comm]
  calc
    ∑ j, ∑ i, x j * y (i - j) * ω ^ ((i : ℤ) * ↑↑k) = ∑ j, ∑ l, x j * y l * ω ^ ((j + l : ℤ) * ↑↑k) := by
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      rw [Fintype.sum_equiv (Equiv.subRightFin j)]
      intro i
      rw [Equiv.subRightFin_apply]
      congr 1
      norm_cast
      apply h.omega_shift
    _ = ∑ j, ∑ l, (x j * ω ^ ((j : ℤ) * k)) * (y l * ω ^ ((l : ℤ) * k)) := by
      simp_rw [add_mul]
      norm_cast
      simp_rw [pow_add]
      group
    _ = ntt ω x k * ntt ω y k := by rw [← Finset.sum_mul_sum]; rfl

theorem ntt_convolution (h : IsPrimitiveRoot ω n) : ntt ω (x ⋆ y) = (ntt ω x) * (ntt ω y) :=
  funext (fun k ↦ ntt_convolution_apply x y h k)

theorem intt_convolution_apply (h : IsPrimitiveRoot ω n) (i : Fin n) : intt ω (x ⋆ y) i = n • (intt ω x) i * (intt ω y) i := by
  simp_rw [intt_as_ntt, ntt_convolution x y h.inv]
  simp only [Pi.mul_apply, nsmul_eq_mul]
  grind

theorem intt_convolution (h : IsPrimitiveRoot ω n) : intt ω (x ⋆ y) = n • (intt ω x) * (intt ω y) :=
  funext (fun k ↦ intt_convolution_apply x y h k)

theorem convolution_ntt_apply (h : IsPrimitiveRoot ω n) (k : Fin n) : ((ntt ω x) ⋆ (ntt ω y)) k = n • ntt ω (x * y) k := by
  by_cases h0 : n = 0; unfold ntt convolution; subst h0; simp_all
  rw [nsmul_eq_mul]
  calc
    ((ntt ω x) ⋆ (ntt ω y)) k = ∑ i, ntt ω x i * ntt ω y (k - i) := by rfl
    _ = ∑ i, ntt ω x i * ntt ω (fun l ↦ ω ^ (-(i : ℤ) * l) * y l) k := by simp_rw [ntt_shift y k _ h]
    _ = ∑ i : Fin n, (∑ j, x j * ω ^ ((j : ℤ) * i)) * (∑ l : Fin n, ω ^ (-(i : ℤ) * l) * y l * ω ^ ((l : ℤ) * k)) := by rfl
    _ = ∑ i : Fin n, ∑ j, ∑ l : Fin n, x j * ω ^ ((j : ℤ) * i) * (ω ^ (-(i : ℤ) * l) * y l * ω ^ ((l : ℤ) * k)) := by simp [Finset.sum_mul_sum]
    _ = ∑ j, ∑ i : Fin n, ∑ l : Fin n, x j * ω ^ ((j : ℤ) * i) * (ω ^ (-(i : ℤ) * l) * y l * ω ^ ((l : ℤ) * k)) := by rw [Finset.sum_comm]
    _ = ∑ j, ∑ l : Fin n, ∑ i : Fin n, x j * ω ^ ((j : ℤ) * i) * (ω ^ (-(i : ℤ) * l) * y l * ω ^ ((l : ℤ) * k)) := by conv_rhs => arg 2; intro; rw [Finset.sum_comm]
    _ = ∑ j, ∑ l, x j * y l * ω ^ ((l : ℤ) * k) * ∑ i : Fin n, ω ^ ((j : ℤ) * i) * (ω ^ (-(i : ℤ) * l)) := by
      refine Finset.sum_congr rfl (fun j _ ↦ Finset.sum_congr rfl (fun l _ ↦ ?_))
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      ring
    _ = ∑ j, ∑ l, x j * y l * ω ^ ((l : ℤ) * k) * ∑ i : Fin n, ω ^ ((i : ℤ) * (j - l)) := by
      refine Finset.sum_congr rfl (fun j _ ↦ Finset.sum_congr rfl (fun l _ ↦ ?_))
      congr 1
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      rw [← zpow_add₀ (h.ne_zero h0)]
      congr
      ring
    _ = ∑ j, ∑ l, x j * y l * ω ^ ((l : ℤ) * k) * if (n : ℤ) ∣ j - l then n else 0 := by simp_rw [h.sum_zpow_mul_eq]
    _ = ∑ j, x j * y j * ω ^ ((j : ℤ) * k) * n := by simp [cast_divides_helper]
    _ = n * ntt ω (x * y) k := by rw [← Finset.sum_mul, mul_comm]; rfl

theorem convolution_ntt (h : IsPrimitiveRoot ω n) : (ntt ω x) ⋆ (ntt ω y) = n • ntt ω (x * y) :=
  funext (fun k ↦ convolution_ntt_apply x y h k)

theorem convolution_intt (h : IsPrimitiveRoot ω n) (hp : ¬p ∣ n) : (intt ω x) ⋆ (intt ω y) = intt ω (x * y) := by
  simp only [intt_as_ntt', Pi.smul_apply]
  rw [convolution_smul_left, convolution_smul_right, convolution_ntt _ _ h.inv]
  congr 1
  funext i
  simp only [nsmul_eq_mul, Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply, smul_eq_mul]
  rw [inv_mul_eq_iff_eq_mul₀]
  rw [← @ZMod.val_ne_zero, ne_eq, ZMod.val_natCast]
  exact Nat.dvd_iff_mod_eq_zero.mpr.mt hp

theorem convolution_intt_apply (h : IsPrimitiveRoot ω n) (hp : ¬p ∣ n) (i : Fin n) : ((intt ω x) ⋆ (intt ω y)) i = intt ω (x * y) i := by
  rw [convolution_intt x y h hp]

end convolution
