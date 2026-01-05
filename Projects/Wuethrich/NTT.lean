import Mathlib.Algebra.Field.ZMod
import Projects.Wuethrich.Aux
import Projects.Wuethrich.PrimitiveRoots
import Projects.Wuethrich.Convolution

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

theorem ntt_convolution.extracted_1 {n : ℕ} (j a : Fin n) : a - j + j = a := by
  rcases n.eq_zero_or_pos with h | h
  grind
  simp [@Fin.add_def, @Fin.sub_def]
  calc
    ⟨(n - ↑j + ↑a + ↑j) % n, _⟩ = ⟨(n - ↑j + ↑j + ↑a) % n, Nat.mod_lt _ h⟩ := by group
    _ = ⟨(n + ↑a) % n, Nat.mod_lt _ h⟩ := by aesop
    _ = ⟨(n % n + ↑a % n) % n, Nat.mod_lt _ h⟩ := by simp
    _ = ⟨↑a % n, Nat.mod_lt _ h⟩ := by simp
    _ = a := by simp only [Fin.ext_iff];  rw [@Nat.mod_eq_iff]; right; exact ⟨a.2, by simp⟩

theorem ntt_convolution.extracted_2 {n : ℕ} (j a : Fin n) : a + j - j = a := by
  rcases n.eq_zero_or_pos with h | h
  grind
  simp [@Fin.add_def, @Fin.sub_def, ← add_assoc]
  calc
    ⟨(n - ↑j + ↑a + ↑j) % n, _⟩ = ⟨(n - ↑j + ↑j + ↑a) % n, Nat.mod_lt _ h⟩ := by group
    _ = ⟨(n + ↑a) % n, Nat.mod_lt _ h⟩ := by aesop
    _ = ⟨(n % n + ↑a % n) % n, Nat.mod_lt _ h⟩ := by simp
    _ = ⟨↑a % n, Nat.mod_lt _ h⟩ := by simp
    _ = a := by simp only [Fin.ext_iff];  rw [@Nat.mod_eq_iff]; right; exact ⟨a.2, by simp⟩

@[simp]
theorem val_mod_n {n : ℕ} (a : Fin n) : a.val % n = a.val := by
  rw [@Nat.mod_eq_iff]
  right
  exact ⟨a.2, by simp⟩

theorem sub_val_mod {n : ℕ} {a : Fin n} (h : 0 < a.val) : (n - a.val) % n = n - a.val := by
  rw [@Nat.mod_eq_iff]
  right
  constructor
  · grind
  · use 0
    simp

def myEquiv {n : ℕ} (j : Fin n) : Fin n ≃ Fin n where
  toFun l := l - j
  invFun l := l + j
  left_inv i := by simp [ntt_convolution.extracted_1]
  right_inv i := by simp [ntt_convolution.extracted_2]

theorem ntt_convolution (x : Fin n → ZMod p) (y : Fin n → ZMod p) (hω : IsPrimitiveRoot ω n) :
    ntt ω (convolution x y) = (ntt ω x) * (ntt ω y) := by
  funext k
  simp only [Pi.mul_apply]
  calc
    ntt ω (convolution x y) k = ∑ i, (∑ j, x j * y (i - j)) * ω ^ ((i : ℤ) * ↑↑k) := by rfl
    _ = ∑ i, ∑ j, x j * y (i - j) * ω ^ ((i : ℤ) * ↑↑k) := by simp_rw [Finset.sum_mul]
    _ = ∑ j, ∑ i, x j * y (i - j) * ω ^ ((i : ℤ) * ↑↑k) := Finset.sum_comm
    _ = ∑ j, ∑ l, x j * y l * ω ^ ((j + l : ℤ) * ↑↑k) := by
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      rw [Fintype.sum_equiv (myEquiv j)]
      · intro i
        simp only [myEquiv, Equiv.coe_fn_mk]
        congr 1
        rw [@Fin.coe_sub, @Nat.add_mod_eq_sub]
        simp only [val_mod_n]
        split_ifs with h
        · rcases j.val.eq_zero_or_pos with h | h
          · simp_all
          · simp only [sub_val_mod h, tsub_zero, Nat.cast_add, Fin.is_le', Nat.cast_sub]
            ring_nf
            norm_cast
            rw [pow_add, pow_mul' ω k.val n, hω.pow_eq_one]
            simp
        · congr
          have : j.val > 0 := by contrapose h; simp_all
          grind [sub_val_mod]
    _ = ∑ j, ∑ l, (x j * ω ^ ((j : ℤ) * k)) * (y l * ω ^ ((l : ℤ) * k)) := by simp [add_mul]; norm_cast; simp [pow_add]; grind
    _ = ntt ω x k * ntt ω y k := by rw [← Finset.sum_mul_sum]; rfl
