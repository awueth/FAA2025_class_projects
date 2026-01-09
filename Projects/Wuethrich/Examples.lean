import Projects.Wuethrich.FNTT
import Projects.Wuethrich.Convolution
import Mathlib.Data.Nat.Prime.Defs

instance : Fact (Nat.Prime 5) := by decide
instance : Fact (Nat.Prime 23) := by decide

def p := 17
def ω : ZMod p := 3

instance : Fact (Nat.Prime p) := by decide

#eval ω ^ 16

example : IsPrimitiveRoot ω 16 := by
  constructor
  · decide
  · sorry



def vec1 : Vector (ZMod p) (2 ^ 4) := #v[1, 0, 2, 3, 2, 2, 1, 0, 1, 2, 3, 4, 5, 3, 2, 4]
def vec2 : Vector (ZMod p) (2 ^ 4) := #v[4, 0, 3, 5, 4, 3, 2, 1, 1, 2, 3, 4, 2, 4, 4, 0]

/-
#eval vec1.fntt ω
#eval vec2.fntt ω
#eval vMul vec1 vec2
#eval vConvolution vec1 vec2
#eval (vMul (vec1.fntt ω) (vec2.fntt ω)).ifntt ω
#eval vConvolution vec1 vec2 = (vMul (vec1.fntt ω) (vec2.fntt ω)).ifntt ω
-/
