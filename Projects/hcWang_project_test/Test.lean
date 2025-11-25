import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

theorem test_pass (a b : Nat) : a + b = b + a := by
  omega

theorem test_sorry (a b : Nat) : a * b = b * a := by
  sorry

theorem handshaking_lemma {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (Finset.univ.sum (fun v => G.degree v)) := by
  sorry

#lint
