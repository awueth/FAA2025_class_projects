import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Fintype.BigOperators

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
      | inl val =>
        simp [Fin.double]
        rw [@Fin.mod_def]
        simp_all
        cases n with
        | zero => simp
        | succ =>
          rw [Nat.mod_eq_of_lt (a := 2) (lt_self_pow₀ one_lt_two (Nat.one_lt_succ_succ _))]
          simp
      | inr val =>
        simp [Fin.doubleSucc]
        rw [@Fin.mod_def]
        simp_all
        cases n with
        | zero => simp
        | succ =>
          rw [Nat.mod_eq_of_lt (a := 2) (lt_self_pow₀ one_lt_two (Nat.one_lt_succ_succ _))]
          simp
  right_inv x := by
    simp
    split_ifs with h
    · rw [Sum.elim_inl, Fin.double]
      rw [Fin.mod_def, Fin.mk_eq_zero] at h
      congr
      refine Nat.two_mul_div_two_of_even ?_
      rw [@Nat.even_iff]
      cases n with
      | zero => simp_all
      | succ n =>
        have : (2 : Fin (2 ^ (n + 1 + 1))).val = 2 := by
          rw [Fin.coe_ofNat_eq_mod]
          exact Nat.mod_eq_of_lt (a := 2) (lt_self_pow₀ one_lt_two (by omega))
        rw [this] at h
        exact h
    · simp only [Sum.elim_inr, Fin.doubleSucc]
      apply Fin.eq_of_val_eq
      rw [Fin.mod_def, Fin.mk_eq_zero] at h
      cases n with
      | zero => grind
      | succ n =>
        have : (2 : Fin (2 ^ (n + 1 + 1))).val = 2 := by
          rw [Fin.coe_ofNat_eq_mod]
          exact Nat.mod_eq_of_lt (a := 2) (lt_self_pow₀ one_lt_two (by omega))
        rw [this] at h
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

end Fin

section Vector

variable {α : Type} {n : ℕ}

def Vector.restrictEven (xs : Vector α (2 ^ (n + 1))) : Vector α (2 ^ n) :=
  Vector.ofFn (fun i ↦ xs.get ⟨2 * i.val, by omega⟩)

def Vector.restrictOdd (xs : Vector α (2 ^ (n + 1))) : Vector α (2 ^ n) :=
  Vector.ofFn (fun i ↦ xs.get ⟨2 * i.val + 1, by omega⟩)

lemma ok_even {xs : Vector α (2 ^ (n + 1))} :
    restrictEven (fun i => xs.get i) = fun i => xs.restrictEven.get i := by
  funext j
  simp [restrictEven, Fin.double, Vector.restrictEven]

lemma ok_odd {xs : Vector α (2 ^ (n + 1))} :
    restrictOdd (fun i => xs.get i) = fun i => xs.restrictOdd.get i := by
  funext j
  simp [restrictOdd, Fin.doubleSucc, Vector.restrictOdd]

def Vector.zipWith3 {α β γ δ : Type*} {n : ℕ} (f : α → β → γ → δ)
    (v1 : Vector α n) (v2 : Vector β n) (v3 : Vector γ n) : Vector δ n :=
  Vector.ofFn (fun i => f (v1.get i) (v2.get i) (v3.get i))

end Vector

lemma cast_divides_helper {n : ℕ} (k l : Fin n) : ↑n ∣ (l : ℤ) - ↑k ↔ l = k := by
  constructor
  · intro hd
    by_contra hc
    wlog hl : k < l generalizing k l
    · grind [dvd_sub_comm]
    · apply Int.le_of_dvd (by omega) at hd
      omega
  · simp_all
