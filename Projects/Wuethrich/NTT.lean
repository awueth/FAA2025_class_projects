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

def Equiv.subRightFin {n : ℕ} (j : Fin n) : Fin n ≃ Fin n where
  toFun l := l - j
  invFun l := l + j
  left_inv i := by
    rcases n.eq_zero_or_pos with h | h
    · grind
    · simp only [Fin.sub_def, Fin.add_def, Nat.mod_add_mod]
      calc
        ⟨(n - ↑j + ↑i + ↑j) % n, _⟩ = ⟨(n - ↑j + ↑j + ↑i) % n, Nat.mod_lt _ h⟩ := by group
        _ = ⟨(n + ↑i) % n, Nat.mod_lt _ h⟩ := by simp
        _ = ⟨(n % n + ↑i % n) % n, Nat.mod_lt _ h⟩ := by simp
        _ = ⟨↑i % n, Nat.mod_lt _ h⟩ := by simp
        _ = i := by simp only [Fin.ext_iff, Nat.mod_eq_iff]; exact Or.inr ⟨i.2, by simp⟩
  right_inv i := by
    rcases n.eq_zero_or_pos with h | h
    · grind
    · simp only [Fin.add_def, Fin.sub_def, Nat.add_mod_mod, ← add_assoc]
      calc
        ⟨(n - ↑j + ↑i + ↑j) % n, _⟩ = ⟨(n - ↑j + ↑j + ↑i) % n, Nat.mod_lt _ h⟩ := by group
        _ = ⟨(n + ↑i) % n, Nat.mod_lt _ h⟩ := by simp
        _ = ⟨(n % n + ↑i % n) % n, Nat.mod_lt _ h⟩ := by simp
        _ = ⟨↑i % n, Nat.mod_lt _ h⟩ := by simp
        _ = i := by simp only [Fin.ext_iff, Nat.mod_eq_iff]; exact Or.inr ⟨i.2, by simp⟩

@[simp]
def Equiv.subRightFin_apply {n : ℕ} (i j : Fin n) : Equiv.subRightFin i j = j - i := by rfl

lemma omega_shift {n : ℕ} {ω : ZMod p} (h : IsPrimitiveRoot ω n) (i j k : Fin n) :
     ω ^ (i.val * k.val) = ω ^ ((j.val + (i - j).val) * k.val) := by
  rw [@Fin.coe_sub, @Nat.add_mod_eq_sub]
  simp only [val_mod_n]
  split_ifs with hi
  · rcases j.val.eq_zero_or_pos with h0 | h0
    · simp_all
    · simp only [sub_val_mod h0, tsub_zero]
      have : ↑j + (n - ↑j + ↑i) = n + ↑i := by
        zify [j.2]
        ring
      rw [this]
      ring_nf
      simp [pow_mul' ω k.val n, h.pow_eq_one]
  · congr
    have : j.val > 0 := by contrapose hi; simp_all
    grind [sub_val_mod]

theorem ntt_convolution (x : Fin n → ZMod p) (y : Fin n → ZMod p) (hω : IsPrimitiveRoot ω n) :
    ntt ω (convolution x y) = (ntt ω x) * (ntt ω y) := by
  funext k
  conv_lhs => simp only [Pi.mul_apply, ntt, convolution, Finset.sum_mul]; rw [Finset.sum_comm]
  calc
    ∑ j, ∑ i, x j * y (i - j) * ω ^ ((i : ℤ) * ↑↑k) = ∑ j, ∑ l, x j * y l * ω ^ ((j + l : ℤ) * ↑↑k) := by
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      rw [Fintype.sum_equiv (Equiv.subRightFin j)]
      intro i
      rw [Equiv.subRightFin_apply]
      congr 1
      norm_cast
      apply omega_shift hω
    _ = ∑ j, ∑ l, (x j * ω ^ ((j : ℤ) * k)) * (y l * ω ^ ((l : ℤ) * k)) := by
      simp_rw [add_mul]
      norm_cast
      simp_rw [pow_add]
      group
    _ = ntt ω x k * ntt ω y k := by rw [← Finset.sum_mul_sum]; rfl

theorem intt_convolution (x : Fin n → ZMod p) (y : Fin n → ZMod p) (hω : IsPrimitiveRoot ω n) :
    intt ω (convolution x y) = n * (intt ω x) * (intt ω y) := by
  funext k
  by_cases h0 : n = 0
  · unfold intt intt_aux convolution
    simp_all
  · simp only [Pi.mul_apply, Pi.natCast_apply]
    unfold intt
    field_simp
    congr
    conv_lhs => simp only [intt_aux, convolution, Finset.sum_mul]; rw [Finset.sum_comm]
    calc
      ∑ j, ∑ i, x j * y (i - j) * ω ^ (-((i : ℤ) * ↑↑k)) = ∑ j, ∑ l, x j * y l * ω ^ (-((j + l : ℤ) * ↑↑k)) := by
        refine Finset.sum_congr rfl (fun j _ ↦ ?_)
        rw [Fintype.sum_equiv (Equiv.subRightFin j)]
        intro i
        rw [Equiv.subRightFin_apply]
        congr 1
        rw [zpow_neg, zpow_neg]
        congr 1
        norm_cast
        apply omega_shift hω
      _ = ∑ j, ∑ l, (x j * ω ^ (-((j : ℤ) * k))) * (y l * ω ^ (-((l : ℤ) * k))) := by
        simp_rw [add_mul, neg_add]
        simp_rw [zpow_add₀ (hω.ne_zero h0)]
        group
      _ = intt_aux ω x k * intt_aux ω y k := by rw [← Finset.sum_mul_sum]; rfl

theorem convolution_ntt (x : Fin n → ZMod p) (y : Fin n → ZMod p) (hω : IsPrimitiveRoot ω n) :
    convolution (ntt ω x) (ntt ω y) = n * ntt ω (x * y) := by
  funext k
  by_cases h0 : n = 0; unfold ntt convolution; subst h0; simp_all
  calc
    convolution (ntt ω x) (ntt ω y) k = ∑ i, ntt ω x i * ntt ω y (k - i) := by rfl
    _ = ∑ i, ntt ω x i * ntt ω (fun l ↦ ω ^ (-(i : ℤ) * l) * y l) k := by simp_rw [ntt_shift y k _ hω]
    _ = ∑ i : Fin n, (∑ j, x j * ω ^ ((j : ℤ) * i)) * (∑ l : Fin n, ω ^ (-(i : ℤ) * l) * y l * ω ^ ((l : ℤ) * k)) := by rfl
    _ = ∑ i : Fin n, ∑ j, ∑ l : Fin n, x j * ω ^ ((j : ℤ) * i) * (ω ^ (-(i : ℤ) * l) * y l * ω ^ ((l : ℤ) * k)) := by simp [Finset.sum_mul_sum]
    _ = ∑ j, ∑ i : Fin n, ∑ l : Fin n, x j * ω ^ ((j : ℤ) * i) * (ω ^ (-(i : ℤ) * l) * y l * ω ^ ((l : ℤ) * k)) := by rw [Finset.sum_comm]
    _ = ∑ j, ∑ l : Fin n, ∑ i : Fin n, x j * ω ^ ((j : ℤ) * i) * (ω ^ (-(i : ℤ) * l) * y l * ω ^ ((l : ℤ) * k)) := by conv_rhs => arg 2; intro; rw [Finset.sum_comm]
    _ = ∑ j, ∑ l, x j * y l * ω ^ ((l : ℤ) * k) * ∑ i : Fin n, ω ^ ((j : ℤ) * i) * (ω ^ (-(i : ℤ) * l)) := by
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      refine Finset.sum_congr rfl (fun l _ ↦ ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      ring
    _ = ∑ j, ∑ l, x j * y l * ω ^ ((l : ℤ) * k) * ∑ i : Fin n, ω ^ ((i : ℤ) * (j - l)) := by
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      refine Finset.sum_congr rfl (fun l _ ↦ ?_)
      congr 1
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      rw [← zpow_add₀ (hω.ne_zero h0)]
      congr
      ring
    _ = ∑ j, ∑ l, x j * y l * ω ^ ((l : ℤ) * k) * if (n : ℤ) ∣ j - l then n else 0 := by simp_rw [hω.sum_zpow_mul_eq]
    _ = ∑ j, x j * y j * ω ^ ((j : ℤ) * k) * n := by simp [cast_divides_helper]
    _ = n * ntt ω (x * y) k := by rw [← Finset.sum_mul, mul_comm]; rfl
