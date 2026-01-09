import Mathlib.Tactic
import Projects.Wuethrich.List

universe u v w
variable {α : Type u} {δ : Type v} {β γ : Type*}

namespace Array

@[specialize]
def zipWith3MAux {m : Type v → Type w} [Monad m]
    (as : Array α) (bs : Array β) (cs : Array γ)
    (f : α → β → γ → m δ)
    (i : Nat) (ds : Array δ) : m (Array δ) := do
  if h₁ : i < as.size then
    let a := as[i]
    if h₂ : i < bs.size then
      let b := bs[i]
      if h₃ : i < cs.size then
        let c := cs[i]
        zipWith3MAux as bs cs f (i+1) <| ds.push (← f a b c)
      else
        return ds
    else
      return ds
  else
    return ds
decreasing_by simp_wf; decreasing_trivial_pre_omega

@[inline] def zipWith3 (f : α → β → γ → δ) (as : Array α) (bs : Array β) (cs : Array γ) : Array δ :=
  Id.run (zipWith3MAux as bs cs (pure <| f · · ·) 0 #[])

@[simp, grind =] theorem zipWith3_toArray (as : List α) (bs : List β) (cs : List γ) (f : α → β → γ → δ) :
    Array.zipWith3 f as.toArray bs.toArray cs.toArray = (List.zipWith3 f as bs cs).toArray := by
  rw [Array.zipWith3]
  --simp [zipWithMAux_toArray_zero, ← zipWithM'_eq_zipWithM]
  sorry

@[simp] theorem toList_zipWith3 {f : α → β → γ → δ} {xs : Array α} {ys : Array β} {zs : Array γ} :
    (zipWith3 f xs ys zs).toList = List.zipWith3 f xs.toList ys.toList zs.toList := by
  cases xs
  cases ys
  cases zs
  simp

@[simp] theorem size_zipWith3 {xs : Array α} {ys : Array β} {zs : Array γ} {f : α → β → γ → δ} :
    (zipWith3 f xs ys zs).size = min (min xs.size ys.size) zs.size := by
  rw [size_eq_length_toList, toList_zipWith3, List.length_zipWith3]
  simp only [Array.size]

@[simp, grind =] theorem getElem_zipWith3 {xs : Array α} {ys : Array β} {zs : Array γ} {f : α → β → γ → δ} {i : Nat}
    (hi : i < (zipWith3 f xs ys zs).size) :
    (zipWith3 f xs ys zs)[i] = f (xs[i]'(by simp at hi; omega)) (ys[i]'(by simp at hi; omega)) (zs[i]'(by simp at hi; omega)) := by
  cases xs
  cases ys
  cases zs
  simp
