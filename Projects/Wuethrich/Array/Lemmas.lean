import Projects.Wuethrich.Array.Basic
import Projects.Wuethrich.List.Zip
import Projects.Wuethrich.List.toArray

variable {α β γ δ : Type*}

namespace Array

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
