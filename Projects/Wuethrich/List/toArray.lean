import Projects.Wuethrich.Array.Basic
import Projects.Wuethrich.List.Zip

universe u v w
variable {α : Type u} {δ : Type v} {β γ : Type*}

namespace List

open Array

theorem zipWith3MAux_toArray_succ {m : Type v → Type w} [Monad m]
    (as : List α) (bs : List β) (cs : List γ) (f : α → β → γ → m δ) (i : Nat) (xs : Array δ) :
    zipWith3MAux as.toArray bs.toArray cs.toArray f (i + 1) xs =
      zipWith3MAux as.tail.toArray bs.tail.toArray cs.tail.toArray f i xs := by
  rw [zipWith3MAux]
  conv => rhs; rw [zipWith3MAux]
  simp only [size_toArray, getElem_toArray, length_tail, getElem_tail]
  split <;> rename_i h₁
  · split <;> rename_i h₂
    · split <;> rename_i h₃
      · rw [dif_pos (by omega), dif_pos (by omega), dif_pos (by omega)]
        simp only [zipWith3MAux_toArray_succ as bs cs f (i+1)]
      · rw [dif_pos (by omega), dif_pos (by omega)]
        rw [dif_neg (by omega)]
    · rw [dif_pos (by omega)]
      rw [dif_neg (by omega)]
  · rw [dif_neg (by omega)]


theorem zipWith3MAux_toArray_succ' {m : Type v → Type w} [Monad m]
    (as : List α) (bs : List β) (cs : List γ)
    (f : α → β → γ → m δ) (i : Nat) (xs : Array δ) :
    zipWith3MAux as.toArray bs.toArray cs.toArray f (i + 1) xs =
      zipWith3MAux (as.drop (i+1)).toArray (bs.drop (i+1)).toArray (cs.drop (i+1)).toArray f 0 xs := by
  induction i generalizing as bs cs xs with
  | zero => simp [zipWith3MAux_toArray_succ]
  | succ i ih =>
    rw [zipWith3MAux_toArray_succ, ih]
    simp

theorem zipWith3MAux_toArray_zero {m : Type v → Type w} [Monad m] [LawfulMonad m] (f : α → β → γ → m δ) (as : List α) (bs : List β) (cs : List γ) (xs : Array δ) :
    Array.zipWith3MAux as.toArray bs.toArray cs.toArray f 0 xs = do return xs ++ (← List.zipWith3M f as bs cs).toArray := by
  rw [Array.zipWith3MAux]
  match as, bs, cs with
  | [], _, _ => simp
  | _, [], _ => simp
  | _, _, [] => simp
  | a :: as, b :: bs, c :: cs =>
    simp [zipWith3MAux_toArray_succ', zipWith3MAux_toArray_zero]


@[simp, grind =] theorem zipWith3_toArray (as : List α) (bs : List β) (cs : List γ) (f : α → β → γ → δ) :
    Array.zipWith3 f as.toArray bs.toArray cs.toArray = (List.zipWith3 f as bs cs).toArray := by
  rw [Array.zipWith3]
  simp [zipWith3MAux_toArray_zero, ← zipWith3M'_eq_zipWith3M]
