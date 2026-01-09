import Mathlib.Tactic

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
