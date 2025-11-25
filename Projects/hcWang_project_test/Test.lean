import Mathlib.Tactic

theorem test_pass (a b : Nat) : a + b = b + a := by
  omega

theorem test_sorry (a b : Nat) : a * b = b * a := by
  sorry
