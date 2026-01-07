import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.GeomSum

variable {M : Type} [CommMonoid M] {ω : M}

namespace IsPrimitiveRoot

theorem pow_two_of_even_order {k : ℕ} (hk : Even k) (h : IsPrimitiveRoot ω k) :
    IsPrimitiveRoot (ω ^ 2) (k / 2) := by
  constructor
  · rw [← pow_mul, Nat.two_mul_div_two_of_even hk, h.pow_eq_one]
  · intro l hl
    rw [← pow_mul] at hl
    rw [Nat.div_dvd_iff_dvd_mul (even_iff_two_dvd.mp hk) zero_lt_two]
    exact h.dvd_of_pow_eq_one (2 * l) hl

lemma of_pow_two {n : ℕ} (h : IsPrimitiveRoot ω (2 ^ (n + 1))) :
    IsPrimitiveRoot (ω ^ 2) (2 ^ n) := by
  convert h.pow_two_of_even_order ((Nat.even_pow' (Nat.succ_ne_zero n)).mpr even_two) using 1
  rw [Nat.pow_succ, Nat.mul_div_cancel _ zero_lt_two]

variable {n p : ℕ} [Fact p.Prime]

lemma sum_zpow_mul_eq {m : ℤ} {ω : ZMod p} (h : IsPrimitiveRoot ω n) :
    ∑ k : Fin n, ω ^ (k * m) = if (n : ℤ) ∣ m then n else 0 := by
  simp_rw [mul_comm, zpow_mul]
  split_ifs with hd
  · simp [(IsPrimitiveRoot.zpow_eq_one_iff_dvd h m).mpr hd]
  · rw [Fin.sum_univ_eq_sum_range (fun x ↦ (ω ^ m) ^ (x : ℤ))]
    have h_ne_one : ω ^ m ≠ 1 := mt (IsPrimitiveRoot.zpow_eq_one_iff_dvd h m).mp hd
    norm_cast
    rw [geom_sum_eq h_ne_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
     h.zpow_eq_one, one_zpow, sub_self, zero_div]

variable {ω : ZMod p}

lemma pow_two_fin_of_nat (h : IsPrimitiveRoot ω (2 ^ (n + 1))) (k : Fin (2 ^ (n + 1))) :
    (ω ^ 2) ^ ((Fin.ofNat (2 ^ n) k) : ℕ) = ω ^ (2 * k : ℕ)  := by
  simp only [Fin.ofNat_eq_cast, Fin.val_natCast]
  nth_rw 2 [← Nat.mod_add_div k (2 ^ n)]
  ring_nf
  refine (mul_right_eq_self₀.mpr (Or.inl ?_)).symm
  rw [mul_assoc, ← pow_succ, pow_mul', h.pow_eq_one, one_pow]

lemma pow_eq_neg_one (h : IsPrimitiveRoot ω (2 ^ (n + 1))) : ω ^ (2 ^ n) = -1 := by
  refine (sq_eq_one_iff.mp ?_).resolve_left ?_
  · rw [← @pow_mul]
    apply h.pow_eq_one
  · rw [h.pow_eq_one_iff_dvd]
    cases n with
    | zero => simp
    | succ n =>
      apply Nat.not_dvd_of_pos_of_lt (pow_pos (by decide) _)
      gcongr
      all_goals simp
