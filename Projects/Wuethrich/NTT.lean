import Mathlib.Algebra.Field.ZMod
import Projects.Wuethrich.Aux
import Projects.Wuethrich.PrimitiveRoots


variable {n p : ℕ} [Fact p.Prime] (ω : ZMod p)

def ntt : (Fin n → ZMod p) → (Fin n → ZMod p) :=
  fun x k ↦ ∑ j, x j * ω ^ ((j * k) : ℤ)

def intt_aux : (Fin n → ZMod p) → (Fin n → ZMod p) :=
  fun x k ↦ ∑ j, x j * ω ^ (-(j * k : ℤ))

def intt : (Fin n → ZMod p) → (Fin n → ZMod p) :=
  fun x k ↦ (n : ZMod p)⁻¹ * (intt_aux ω x k)

lemma left_inv_aux (hn0 : n ≠ 0) (h : IsPrimitiveRoot ω n) (x : Fin n → ZMod p) :
    intt_aux ω (ntt ω x) = n * x := by
  unfold ntt intt_aux
  funext k
  simp_rw [Finset.sum_mul, mul_assoc,
   ← zpow_add' (Or.inl (IsPrimitiveRoot.ne_zero h hn0))]
  conv => left; arg 2; intro j; arg 2; intro l; arg 2; arg 2; ring_nf; rw [mul_comm, ← mul_sub]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, h.sum_zpow_mul_eq]
  simp [cast_divides_helper, mul_comm]

lemma right_inv_aux (hn0 : n ≠ 0) (h : IsPrimitiveRoot ω n) (x : Fin n → ZMod p) :
    ntt ω (intt_aux ω x) = n * x := by
  unfold ntt intt_aux
  funext k
  simp only [Pi.mul_apply, Pi.natCast_apply]
  calc
    ∑ i : Fin n, (∑ j, x j * ω ^ (-((j : ℤ) * i))) * ω ^ ((i : ℤ) * k) =
      ∑ i : Fin n, ∑ j, x j * ω ^ (-((j : ℤ) * i) + i * k) := by
      simp_rw [Finset.sum_mul, mul_assoc, ← zpow_add' (Or.inl (IsPrimitiveRoot.ne_zero h hn0))];
    _ = ∑ i : Fin n, ∑ j, x j * ω ^ (i * ((k : ℤ) - j)) := by rcongr; ring
    _ = ∑ j, x j * ∑ i : Fin n,  ω ^ (i * ((k : ℤ) - j)) := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ j : Fin n, x j * ↑(if ↑n ∣ (↑k : ℤ) - j then n else 0) := by simp_rw [h.sum_zpow_mul_eq];
    _ = n * x k := by simp [cast_divides_helper, mul_comm]

theorem left_inv (hn0 : n ≠ 0) (hp : ¬p ∣ n) (h : IsPrimitiveRoot ω n) (x : Fin n → ZMod p) :
    intt ω (ntt ω x) = x := by
  unfold intt
  funext k
  rw [inv_mul_eq_iff_eq_mul₀]
  · exact congrFun (left_inv_aux ω hn0 h x) k
  · rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hp

theorem right_inv (hn0 : n ≠ 0) (hp : ¬p ∣ n) (h : IsPrimitiveRoot ω n) (x : Fin n → ZMod p) :
    ntt ω (intt ω x) = x := by
  unfold ntt intt
  funext k
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [inv_mul_eq_iff_eq_mul₀]
  · exact congrFun (right_inv_aux ω hn0 h x) k
  · rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hp
