import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring.RingNF

section Fin

variable {M : Type} [AddCommMonoid M]
variable {p : ℕ}

-- Embed `i : Fin (2^n)` into `Fin (2^(n+1))` as the even index `2 * i`.
def Fin.double {n : ℕ} (i : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) := ⟨2 * i.val, by omega⟩

-- Embed `i : Fin (2^n)` into `Fin (2^(n+1))` as the odd index `2 * i + 1`.
def Fin.doubleSucc {n : ℕ} (i : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) := ⟨2 * i.val + 1, by omega⟩

-- Restriction to even indices.
def restrictEven {n : ℕ} : (Fin (2 ^ (n + 1)) → M) → (Fin (2 ^ n) → M) :=
  fun x k ↦ x k.double

-- Restriction to odd indices.
def restrictOdd {n : ℕ} : (Fin (2 ^ (n + 1)) → M) → (Fin (2 ^ n) → M) :=
  fun x k ↦ x k.doubleSucc

/- Equivalence between `Fin (2 ^ n) m ⊕ Fin (2 ^ n)` and `Fin (2 ^ (n + 1))` -/
def finTwoPowSuccEquiv {n : ℕ} : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) where
  toFun := Sum.elim (Fin.double) (Fin.doubleSucc)
  invFun i :=
    if h : i % 2 = 0 then
      Sum.inl ⟨i.val / 2, by omega⟩
    else
      Sum.inr ⟨(i.val - 1) / 2, by omega⟩
  left_inv x := by
    · cases x with
      | inl val
      | inr val =>
        simp [Fin.double, Fin.doubleSucc, @Fin.mod_def]
        cases n with
        | zero => simp
        | succ => simp [Nat.mod_eq_of_lt (lt_self_pow₀ one_lt_two (Nat.one_lt_succ_succ _))]
  right_inv x := by
    unfold Fin.double Fin.doubleSucc
    simp only [dite_eq_ite]
    split_ifs with h
    all_goals (apply Fin.ext; rw [Sum.elim])
    · apply Nat.two_mul_div_two_of_even
      rw [@Nat.even_iff]
      rw [Fin.mod_def] at h
      simp_all
      cases n with
      | zero => simp_all
      | succ n =>
        rw [Nat.mod_eq_of_lt (a := 2) (lt_self_pow₀ one_lt_two (Nat.one_lt_succ_succ n))] at h
        simp_all
    · rw [Fin.mod_def, Fin.mk_eq_zero] at h
      cases n with
      | zero => grind
      | succ n =>
        simp [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (lt_self_pow₀ one_lt_two (Nat.one_lt_succ_succ _))] at h
        grind

lemma sum_even_odd_split {n : ℕ} (f : Fin (2 ^ (n + 1)) → M) :
    ∑ i : Fin (2 ^ (n + 1)), f i
     = ∑ j : Fin (2 ^ n), f j.double +
       ∑ j : Fin (2 ^ n), f j.doubleSucc := by
  rw [Fintype.sum_equiv finTwoPowSuccEquiv.symm f fun i => f (finTwoPowSuccEquiv.toFun i)]
  · simp_all
    rfl
  · intro i
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]

def Equiv.subRightFin {n : ℕ} (j : Fin n) : Fin n ≃ Fin n where
  toFun l := l - j
  invFun l := l + j
  left_inv i := by
    rcases n.eq_zero_or_pos with h | h
    · grind
    · simp only [Fin.sub_def, Fin.add_def, Nat.mod_add_mod]
      calc
        ⟨(n - ↑j + ↑i + ↑j) % n, _⟩ = ⟨(n - ↑j + ↑j + ↑i) % n, Nat.mod_lt _ h⟩ := by ring_nf
        _ = ⟨(n + ↑i) % n, Nat.mod_lt _ h⟩ := by simp
        _ = ⟨(n % n + ↑i % n) % n, Nat.mod_lt _ h⟩ := by simp
        _ = ⟨↑i % n, Nat.mod_lt _ h⟩ := by simp
        _ = i := by simp only [Fin.ext_iff, Nat.mod_eq_iff]; exact Or.inr ⟨i.2, by simp⟩
  right_inv i := by
    rcases n.eq_zero_or_pos with h | h
    · grind
    · simp only [Fin.ext_iff, Fin.add_def, Fin.sub_def, Nat.add_mod_mod, ← add_assoc]
      calc
        (n - ↑j + ↑i + ↑j) % n = (n - ↑j + ↑j + ↑i) % n := by ring_nf
        _ = (n + ↑i) % n := by simp
        _ = (n % n + ↑i % n) % n := by simp
        _ = ↑i % n:= by simp
        _ = i := by simp only [Nat.mod_eq_iff]; exact Or.inr ⟨i.2, by simp⟩

@[simp]
def Equiv.subRightFin_apply {n : ℕ} (i j : Fin n) : Equiv.subRightFin i j = j - i := by rfl

@[simp]
theorem val_mod_n {n : ℕ} (a : Fin n) : a.val % n = a.val := Nat.mod_eq_of_lt a.2

theorem sub_val_mod {n : ℕ} {a : Fin n} (h : 0 < a.val) : (n - a.val) % n = n - a.val := by
  rw [Nat.mod_eq_of_lt]
  omega

end Fin

lemma cast_divides_helper {n : ℕ} (k l : Fin n) : ↑n ∣ (l : ℤ) - ↑k ↔ l = k := by
  constructor
  · intro hd
    by_contra hc
    wlog hl : k < l generalizing k l
    · grind [dvd_sub_comm]
    · apply Int.le_of_dvd (by omega) at hd
      omega
  · simp_all
