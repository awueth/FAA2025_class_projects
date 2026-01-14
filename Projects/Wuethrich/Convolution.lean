import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.GroupTheory.GroupAction.Ring

section tuple

variable {n : ℕ} {R : Type} [Ring R] (x y : Fin n → R)

/-- Circular convolution

For tuples `x, y : Fin n → R`, `convolution k` is the circular convolution at index `k`,
defined by summing x j * y (k - j) over j. The subtraction and indexing are performed in `Fin n`,
so all indices are taken modulo `n`
-/
def convolution : Fin n → R := fun k ↦ ∑ j, x j * y (k - j)

infixl:70 " ⋆ " => convolution

theorem convolution_smul_left (a : R) :  (a • x) ⋆ y = a • (x ⋆ y) := by
  unfold convolution
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

variable {n : ℕ} {R : Type} [CommRing R] (x y : Fin n → R)

theorem convolution_smul_right (a : R) : x ⋆ (a • y) = a • (x ⋆ y) := by
  unfold convolution
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [← mul_assoc, ← mul_assoc, mul_comm a (x j)]

end tuple

section vector

variable {n : ℕ} {R : Type} [Ring R] (x y : Vector R n)

/-- Convolution of two vectors, obtained by converting the vectors to functions on `Fin n`. -/
def Vector.convolution : Vector R n := Vector.ofFn (x.get ⋆ y.get)

theorem Vector.get_convolution : (x.convolution y).get = x.get ⋆ y.get := by
  ext i
  simp [Vector.convolution]

theorem Vector.getElem_convolution {i : ℕ} (h : i < n) : (x.convolution y)[i]'h = (x.get ⋆ y.get) ⟨i, h⟩ := by
  simp [Vector.convolution]

end vector
