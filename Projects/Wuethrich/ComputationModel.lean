/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
import Projects.Wuethrich.Array.Lemmas

set_option autoImplicit false
set_option tactic.hygienic false

structure TimeM (α : Type) where
  ret : α
  time : ℕ

namespace TimeM

def pure {α} (a : α) : TimeM α :=
  ⟨a, 0⟩

def bind {α β} (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance : Monad TimeM where
  pure := pure
  bind := bind

-- Increment time
@[simp] def tick {α : Type} (a : α) (c : ℕ := 1) : TimeM α :=
  ⟨a, c⟩

notation "✓" a:arg ", " c:arg => tick a c
notation "✓" a:arg => tick a  -- Default case with only one argument

def tickUnit : TimeM Unit :=
  ✓ () -- This uses the default time increment of 1

@[grind, simp] theorem time_of_pure {α} (a : α) : (pure a).time = 0 := rfl
@[grind, simp] theorem time_of_bind {α β} (m : TimeM α) (f : α → TimeM β) :
 (TimeM.bind m f).time = m.time + (f m.ret).time := rfl
@[grind, simp] theorem time_of_tick {α} (a : α) (c : ℕ) : (tick a c).time = c := rfl
@[grind, simp] theorem ret_bind {α β} (m : TimeM α) (f : α → TimeM β) :
  (TimeM.bind m f).ret = (f m.ret).ret := rfl

-- allow us to simplify the chain of compositions
attribute [simp] Bind.bind Pure.pure TimeM.pure


end TimeM

variable {m n : ℕ} {α : Type}

-- Does not copy the underlying array
def Vector.castT (h : n = m) (xs : Vector α n) : TimeM (Vector α m) := ⟨xs.cast h, 0⟩

-- Does copy the underlying array
def Vector.extractT  (xs : Vector α n) (start : Nat := 0) (stop : Nat := n) :
    TimeM (Vector α (min stop n - start)) :=
  ⟨xs.extract start stop, n⟩

def Vector.appendT (xs : Vector α n) (ys : Vector α m) : TimeM (Vector α (n + m)) :=
  ⟨xs ++ ys, n⟩

def Vector.restrictEvenT (xs : Vector α (2 ^ (n + 1))) : TimeM (Vector α (2 ^ n)) :=
  ⟨Vector.ofFn (fun i ↦ xs.get ⟨2 * i.val, by omega⟩), 2 ^ n⟩

def Vector.restrictOddT (xs : Vector α (2 ^ (n + 1))) : TimeM (Vector α (2 ^ n)) :=
  ⟨Vector.ofFn (fun i ↦ xs.get ⟨2 * i.val + 1, by omega⟩), 2 ^ n⟩

def Vector.zipWith3T {δ : Type} {α β γ : Type*} {n : ℕ} (f : α → β → γ → δ)
    (v1 : Vector α n) (v2 : Vector β n) (v3 : Vector γ n) : TimeM (Vector δ n) :=
  ⟨⟨Array.zipWith3 f v1.toArray v2.toArray v3.toArray, by simp⟩, n⟩

def Vector.mulT [Mul α] (xs ys : Vector α n) : TimeM (Vector α n) :=
  ⟨xs.mul ys, n⟩
