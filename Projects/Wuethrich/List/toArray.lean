import Projects.Wuethrich.Array.Basic

variable {α β γ δ : Type*}

namespace List

@[simp, grind =] theorem zipWith3_toArray (as : List α) (bs : List β) (cs : List γ) (f : α → β → γ → δ) :
    Array.zipWith3 f as.toArray bs.toArray cs.toArray = (List.zipWith3 f as bs cs).toArray := by
  rw [Array.zipWith3]
  --simp [zipWithMAux_toArray_zero, ← zipWithM'_eq_zipWithM]
  sorry
