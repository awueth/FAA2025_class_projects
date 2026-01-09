import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Nat.Lattice

variable {α β γ δ : Type*}
variable {a : α} {b : β} {c : γ}
variable {as : List α} {bs : List β} {cs : List γ}
variable {f : α → β → γ → δ}

namespace List

@[simp] theorem zipWith3_nil_left  : zipWith3 f [] bs cs = [] := rfl
@[simp] theorem zipWith3_nil_middle : zipWith3 f as [] cs = [] := by simp [zipWith3]
@[simp] theorem zipWith3_nil_right: zipWith3 f as bs [] = [] := by simp [zipWith3]
@[simp] theorem zipWith3_cons_cons : zipWith3 f (a :: as) (b :: bs) (c :: cs) = f a b c :: zipWith3 f as bs cs := rfl

@[simp, grind =] theorem length_zipWith3 {f : α → β → γ → δ} {l₁ : List α} {l₂ : List β} {l₃  : List γ} :
    length (zipWith3 f l₁ l₂ l₃) = min (min (length l₁) (length l₂)) (length l₃) := by
  induction l₁ generalizing l₂ l₃ with
  | nil => simp [zipWith3]
  | cons head₁ tail₁ ih₁ =>
    cases l₂ with
    | nil => simp [zipWith3]
    | cons head₂ tail₂ =>
      cases l₃ with
      | nil => simp [zipWith3]
      | cons head₃ tail₃ =>
        simp only [length_cons, Nat.add_min_add_right, Nat.min_assoc]
        rw [← Nat.min_assoc, ← ih₁]
        simp [zipWith3]

theorem getElem?_zipWith3_eq_some {f : α → β → γ → δ}
    {l₁ : List α} {l₂ : List β} {l₃ : List γ} {w : δ} {i : Nat} :
    (zipWith3 f l₁ l₂ l₃)[i]? = some w ↔
      ∃ x y z, l₁[i]? = some x ∧ l₂[i]? = some y ∧ l₃[i]? = some z ∧ f x y z = w := by
  induction l₁ generalizing l₂ l₃ i with
  | nil => simp [zipWith3]
  | cons head₁ tail₁ ih₁ =>
    cases l₂ with
    | nil => simp
    | cons head₂ tail₂ =>
      cases l₃ with
      | nil => simp
      | cons head₃ tail₃ =>
        cases i <;> simp_all

@[simp, grind =]
theorem getElem_zipWith3 {f : α → β → γ → δ} {l₁ : List α} {l₂ : List β} {l₃  : List γ}
    {i : Nat} {h : i < (zipWith3 f l₁ l₂ l₃).length} :
    (zipWith3 f l₁ l₂ l₃)[i] =
      f (l₁[i]'(by simp_all))
        (l₂[i]'(by simp_all))
        (l₃[i]'(by simp_all)) := by
  rw [← Option.some_inj, ← getElem?_eq_getElem, getElem?_zipWith3_eq_some]
  simp only [length_zipWith3, Nat.min_assoc, lt_inf_iff] at h
  simp_all only [getElem?_pos, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, exists_eq_left']
