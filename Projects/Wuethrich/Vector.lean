import Projects.Wuethrich.Array.Lemmas
import Projects.Wuethrich.Aux

variable {α : Type} {n : ℕ}

def Vector.restrictEven (xs : Vector α (2 ^ (n + 1))) : Vector α (2 ^ n) :=
  Vector.ofFn (fun i ↦ xs.get ⟨2 * i.val, by omega⟩)

def Vector.restrictOdd (xs : Vector α (2 ^ (n + 1))) : Vector α (2 ^ n) :=
  Vector.ofFn (fun i ↦ xs.get ⟨2 * i.val + 1, by omega⟩)

lemma restrictEven_of_vector {xs : Vector α (2 ^ (n + 1))} :
    restrictEven xs.get = xs.restrictEven.get := by
  funext j
  simp [restrictEven, Fin.double, Vector.restrictEven]

lemma restrictOdd_of_vector {xs : Vector α (2 ^ (n + 1))} :
    restrictOdd xs.get = xs.restrictOdd.get := by
  funext j
  simp [restrictOdd, Fin.doubleSucc, Vector.restrictOdd]



namespace Vector

def zipWith3 {α β γ δ : Type*} {n : ℕ} (f : α → β → γ → δ)
    (v1 : Vector α n) (v2 : Vector β n) (v3 : Vector γ n) : Vector δ n :=
  ⟨Array.zipWith3 f v1.toArray v2.toArray v3.toArray, by simp⟩
  --Vector.ofFn (fun i => f (v1.get i) (v2.get i) (v3.get i))

variable {α β γ δ : Type*}

@[simp] theorem mk_zipWith3_mk {f : α → β → γ → δ} {as : Array α} {bs : Array β} {cs : Array γ}
    (h : as.size = n) (h' : bs.size = n) (h'' : cs.size = n) :
    Vector.zipWith3 f (Vector.mk as h) (Vector.mk bs h') (Vector.mk cs h'') =
      Vector.mk (Array.zipWith3 f as bs cs) (by simp [h, h', h'']) := rfl

@[simp, grind =] theorem getElem_zipWith3  {f : α → β → γ → δ} {as : Vector α n} {bs : Vector β n} {cs : Vector γ n} {i : Nat}
    (hi : i < n) : (Vector.zipWith3 f as bs cs)[i] = f as[i] bs[i] cs[i] := by
  cases as
  cases bs
  cases cs
  simp
