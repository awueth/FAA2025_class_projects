import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Basic

variable {R : Type} [Ring R]
variable {n : ℕ} (x : Fin n → R) (y : Fin n → R)

def convolution : Fin n → R := fun k ↦ ∑ j, x j * y (k - j)
