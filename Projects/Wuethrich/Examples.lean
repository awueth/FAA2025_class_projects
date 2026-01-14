import Projects.Wuethrich.FNTT
import Projects.Wuethrich.Convolution
import Mathlib.Data.Nat.Prime.Defs

instance : Fact (Nat.Prime 5) := by decide
instance : Fact (Nat.Prime 23) := by decide

def p := 17
def ω : ZMod p := 3

instance : Fact (Nat.Prime p) := by decide

#eval ω ^ 16

lemma hω : IsPrimitiveRoot ω 16 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  apply orderOf_eq_of_pow_and_pow_div_prime
  · decide
  · decide
  · intro p hp hp'
    have : 1 < p := by
      by_contra h
      simp at h
      interval_cases p
      · contradiction
      · contradiction
    have : p ≤ 16 := Nat.le_of_dvd (by decide) hp'
    interval_cases p
    all_goals decide

def vec1 : Vector (ZMod p) (2 ^ 4) := #v[1, 0, 2, 3, 2, 2, 1, 0, 1, 2, 3, 4, 5, 3, 2, 4]
def vec2 : Vector (ZMod p) (2 ^ 4) := #v[4, 0, 3, 5, 4, 3, 2, 1, 1, 2, 3, 4, 2, 4, 4, 0]


#eval vec1.fntt ω
#eval vec2.fntt ω
#eval vec1.convolution vec2
#eval vec1.fastConvolution vec2 ω
