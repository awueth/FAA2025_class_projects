import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Nat.Lattice

variable {α β γ δ : Type*}
variable {a : α} {b : β} {c : γ}
variable {as : List α} {bs : List β} {cs : List γ}
variable {f : α → β → γ → δ}

namespace List

@[simp] theorem zipWith3_nil_left  : zipWith3 f [] bs cs = [] := rfl
@[simp] theorem zipWith3_nil_middle : zipWith3 f as [] cs = [] := by simp [zipWith3]
@[simp] theorem zipWith3_nil_right: zipWith3 f as bs [] = [] := by simp [zipWith3]
@[simp] theorem zipWith3_cons_cons_cons : zipWith3 f (a :: as) (b :: bs) (c :: cs) = f a b c :: zipWith3 f as bs cs := rfl

@[simp, grind =] theorem length_zipWith3 {f : α → β → γ → δ} {l₁ : List α} {l₂ : List β} {l₃  : List γ} :
    length (zipWith3 f l₁ l₂ l₃) = min (min (length l₁) (length l₂)) (length l₃) := by
  induction l₁ generalizing l₂ l₃ with
  | nil => simp [zipWith3]
  | cons head₁ tail₁ ih₁ =>
    cases l₂ with
    | nil => simp [zipWith3]
    | cons head₂ tail₂ =>
      cases l₃ with
      | nil => simp [zipWith3]
      | cons head₃ tail₃ =>
        simp only [length_cons, Nat.add_min_add_right, Nat.min_assoc]
        rw [← Nat.min_assoc, ← ih₁]
        simp [zipWith3]

theorem getElem?_zipWith3_eq_some {f : α → β → γ → δ}
    {l₁ : List α} {l₂ : List β} {l₃ : List γ} {w : δ} {i : Nat} :
    (zipWith3 f l₁ l₂ l₃)[i]? = some w ↔
      ∃ x y z, l₁[i]? = some x ∧ l₂[i]? = some y ∧ l₃[i]? = some z ∧ f x y z = w := by
  induction l₁ generalizing l₂ l₃ i with
  | nil => simp [zipWith3]
  | cons head₁ tail₁ ih₁ =>
    cases l₂ with
    | nil => simp
    | cons head₂ tail₂ =>
      cases l₃ with
      | nil => simp
      | cons head₃ tail₃ =>
        cases i <;> simp_all

@[simp, grind =]
theorem getElem_zipWith3 {f : α → β → γ → δ} {l₁ : List α} {l₂ : List β} {l₃  : List γ}
    {i : Nat} {h : i < (zipWith3 f l₁ l₂ l₃).length} :
    (zipWith3 f l₁ l₂ l₃)[i] =
      f (l₁[i]'(by simp_all))
        (l₂[i]'(by simp_all))
        (l₃[i]'(by simp_all)) := by
  rw [← Option.some_inj, ← getElem?_eq_getElem, getElem?_zipWith3_eq_some]
  simp only [length_zipWith3, Nat.min_assoc, lt_inf_iff] at h
  simp_all only [getElem?_pos, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, exists_eq_left']

@[simp, grind =]
theorem map_zipWith3 {ε : Type _} {f : δ → ε} {g : α → β → γ → δ}
    {l₁ : List α} {l₂ : List β} {l₃ : List γ} :
    map f (zipWith3 g l₁ l₂ l₃) = zipWith3 (fun x y z => f (g x y z)) l₁ l₂ l₃ := by
  induction l₁ generalizing l₂ l₃ with
  | nil => simp
  | cons hd tl hl =>
    cases l₂
    · simp
    · cases l₃
      · simp
      · simp [hl]


universe u v w x y
variable {m : Type u → Type v}
variable {α : Type w} {β : Type x} {γ : Type y} {δ : Type u}

@[inline, expose]
def zipWith3M [Monad m] (f : α → β → γ → m δ) (as : List α) (bs : List β) (cs : List γ) : m (List δ) :=
  let rec @[specialize] loop
    | a::as, b::bs, c::cs, acc => do loop as bs cs (acc.push (← f a b c))
    | _, _, _, acc => pure acc.toList
  loop as bs cs #[]

@[expose]
def zipWith3M' [Monad m] (f : α → β → γ → m δ) : (xs : List α) → (ys : List β) → (zs : List γ) → m (List δ)
  | x::xs, y::ys, z::zs => do
    let w ← f x y z
    let ws ← zipWith3M' f xs ys zs
    pure (w :: ws)
  | _, _, _ => pure []

@[grind =]
theorem zipWith3M'_eq_zipWith3M [Monad m] [LawfulMonad m]
    {f : α → β → γ → m δ} {l₁ : List α} {l₂ : List β} {l₃ : List γ} :
    zipWith3M' f l₁ l₂ l₃ = zipWith3M f l₁ l₂ l₃ := by
  simp [zipWith3M, go l₁ l₂ l₃ #[]]
where
  go l₁ l₂ l₃ acc :
    zipWith3M.loop f l₁ l₂ l₃ acc = return acc.toList ++ (← zipWith3M' f l₁ l₂ l₃) := by
    fun_induction zipWith3M.loop <;> simp [zipWith3M', *]

@[simp, grind =]
theorem zipWith3M'_eq_mapM_id_zipWith [Monad m] [LawfulMonad m] {f : α → β → γ → m δ} {as : List α} {bs : List β} {cs : List γ} :
    zipWith3M' f as bs cs = mapM id (zipWith3 f as bs cs) := by
  fun_induction zipWith3M' <;> simp [zipWith3, *]

variable {as : List α} {bs : List β} {cs : List γ} {a : α} {b : β} {c : γ}

@[simp, grind =] theorem zipWith3M_nil_left [Monad m] {f : α → β → γ → m δ}  : zipWith3M f [] bs cs = pure (f := m) [] := rfl
@[simp, grind =] theorem zipWith3M_nil_middle [Monad m] {f : α → β → γ → m δ}  : zipWith3M f as [] cs = pure (f := m) [] := by simp only [zipWith3M, zipWith3M.loop]
@[simp, grind =] theorem zipWith3M_nil_right [Monad m] {f : α → β → γ → m δ}  : zipWith3M f as bs [] = pure (f := m) [] := by simp only [zipWith3M, zipWith3M.loop]
@[simp, grind =] theorem zipWith3M_cons_cons_cons [Monad m] [LawfulMonad m] {f : α → β → γ → m δ} {as : List α} {bs : List β} {cs : List γ}  :
    zipWith3M f (a :: as) (b :: bs) (c :: cs) = do return (← f a b c) :: (← zipWith3M f as bs cs) := by
  simp [← zipWith3M'_eq_zipWith3M]
