import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs

section

variable {n : ℕ} {R : Type} [Ring R] (x y : Fin n → R)

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

end

section

variable {n : ℕ} {R : Type} [Ring R] (x y : Vector R n)

def vConvolution : Vector R n := Vector.ofFn (convolution x.get y.get)

def vMul : Vector R n := Vector.ofFn (x.get * y.get)

end
