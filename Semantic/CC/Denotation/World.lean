import Semantic.CC.Semantics.Heap

/-!
# Ahmed world-parametrized step-indexed store

The store model for CC's generic (reference-valued) mutable cells, following the
CoreCapybara development.  A stored relation at level `k` is a *family over all lower
worlds* `(j : Fin k) → World j → Memory → Exp {} → Prop`, so truncation is a pure drop
and the cell agreement in the value relation can be a genuine biconditional against the
content type's denotation — giving both the forward direction (`read`) and the backward
direction (`write`) while staying monotone under store growth.

`alloc x : cell T` types cells for *any* content type `T`, including a bare type variable,
whose meaning is an environment-supplied semantic relation.  Hence the store must map
locations to semantic relations rather than syntactic types, and the only relation store
that is simultaneously growth-monotone, write-capable, and abstract-content-capable is the
world-parametrized one below.  Its very type is defined by recursion on the index, so the
model is inherently step-indexed: reads consume one index.
-/

namespace CC

/-- `World k` maps each location to an optional relation usable at level `k`: a family,
over every lower level `j < k`, of predicates parametrized by a `World j`. -/
def World : Nat → Type
  | k => Nat → Option ((j : Fin k) → World j.val → Memory → Exp {} → Prop)
termination_by k => k
decreasing_by exact j.isLt

/-- `SemRel k`: a relation stored at level `k` — a family, over every lower level, of
predicates parametrized by a lower world. -/
abbrev SemRel (k : Nat) : Type := (j : Fin k) → World j.val → Memory → Exp {} → Prop

/-- The defining equation (well-founded definitions do not reduce definitionally). -/
theorem World.unfold (k : Nat) : World k = (Nat → Option (SemRel k)) := by
  unfold World SemRel
  rfl

/-- Look up a location, casting through the defining equation. -/
def World.lookup {k : Nat} (w : World k) (l : Nat) : Option (SemRel k) :=
  cast (World.unfold k) w l

/-- Build a world from a location map (inverse cast). -/
def World.mk {k : Nat} (f : Nat → Option (SemRel k)) : World k :=
  cast (World.unfold k).symm f

@[simp] theorem World.lookup_mk {k : Nat} (f : Nat → Option (SemRel k)) (l : Nat) :
    (World.mk f).lookup l = f l := by
  simp only [World.lookup, World.mk, cast_cast, cast_eq]

theorem World.mk_lookup {k : Nat} (w : World k) : World.mk (World.lookup w) = w := by
  change cast (World.unfold k).symm (fun l => cast (World.unfold k) w l) = w
  rw [cast_cast, cast_eq]

/-- Worlds are determined by their lookups. -/
theorem World.ext {k : Nat} {w1 w2 : World k} (h : ∀ l, w1.lookup l = w2.lookup l) :
    w1 = w2 := by
  rw [← World.mk_lookup w1, ← World.mk_lookup w2]
  exact congrArg World.mk (funext h)

/-- The empty world: no location is store-typed. -/
def World.empty (k : Nat) : World k := World.mk fun _ => none

@[simp] theorem World.empty_lookup {k : Nat} (l : Nat) : (World.empty k).lookup l = none := by
  simp only [World.empty, World.lookup_mk]

/-- **Truncation** to a lower level: drop the top of each stored family.  A pure
restriction of the `Fin`-index — no content is fabricated. -/
def World.trunc {k j : Nat} (hjk : j ≤ k) (w : World k) : World j :=
  World.mk fun l => (w.lookup l).map fun R (i : Fin j) (wi : World i.val) =>
    R ⟨i.val, Nat.lt_of_lt_of_le i.isLt hjk⟩ wi

@[simp] theorem World.trunc_lookup {k j : Nat} (hjk : j ≤ k) (w : World k) (l : Nat) :
    (w.trunc hjk).lookup l = (w.lookup l).map fun R (i : Fin j) (wi : World i.val) =>
      R ⟨i.val, Nat.lt_of_lt_of_le i.isLt hjk⟩ wi := by
  simp only [World.trunc, World.lookup_mk]

/-- Truncating to the *same* level is the identity. -/
@[simp] theorem World.trunc_self {k : Nat} (hkk : k ≤ k) (w : World k) : w.trunc hkk = w := by
  apply World.ext
  intro l
  rw [World.trunc_lookup]
  cases w.lookup l with
  | none => rfl
  | some R => rfl

/-- Truncations compose. -/
theorem World.trunc_trunc {k j i : Nat} (hkj : j ≤ k) (hji : i ≤ j) (w : World k) :
    (w.trunc hkj).trunc hji = w.trunc (Nat.le_trans hji hkj) := by
  apply World.ext
  intro l
  simp only [World.trunc_lookup]
  cases w.lookup l with
  | none => rfl
  | some R => rfl

@[simp] theorem World.empty_trunc {k j : Nat} (hjk : j ≤ k) :
    (World.empty k).trunc hjk = World.empty j := by
  apply World.ext
  intro l
  simp only [World.trunc_lookup, World.empty_lookup, Option.map_none]

/-- Extend a world with a fresh cell's stored relation (or overwrite an existing one). -/
def World.set {k : Nat} (w : World k) (l : Nat) (R : SemRel k) : World k :=
  World.mk fun l' => if l' = l then some R else w.lookup l'

@[simp] theorem World.set_lookup {k : Nat} (w : World k) (l : Nat) (R : SemRel k) (l' : Nat) :
    (w.set l R).lookup l' = if l' = l then some R else w.lookup l' := by
  simp only [World.set, World.lookup_mk]

/-- **The typed future-world relation** (at a fixed level).  The memory grows and the
store typing only grows (existing cells keep their assigned relation). -/
def WorldLe {k : Nat} (Ψ' : World k) (m' : Memory) (Ψ : World k) (m : Memory) : Prop :=
  m'.subsumes m ∧ ∀ l R, Ψ.lookup l = some R → Ψ'.lookup l = some R

theorem WorldLe.refl {k : Nat} (Ψ : World k) (m : Memory) : WorldLe Ψ m Ψ m :=
  ⟨Memory.subsumes_refl m, fun _ _ h => h⟩

theorem WorldLe.trans {k : Nat} {Ψ1 Ψ2 Ψ3 : World k} {m1 m2 m3}
    (h12 : WorldLe Ψ2 m2 Ψ1 m1) (h23 : WorldLe Ψ3 m3 Ψ2 m2) : WorldLe Ψ3 m3 Ψ1 m1 :=
  ⟨Memory.subsumes_trans h23.1 h12.1, fun l R h => h23.2 l R (h12.2 l R h)⟩

/-- Growing only the memory (same store typing) is a world step. -/
theorem WorldLe.of_subsumes {k : Nat} {Ψ : World k} {m m' : Memory} (h : m'.subsumes m) :
    WorldLe Ψ m' Ψ m :=
  ⟨h, fun _ _ hh => hh⟩

/-- Reflexivity through a same-level truncation. -/
theorem WorldLe.refl_trunc_self {k : Nat} (h : k ≤ k) (w : World k) (m : Memory) :
    WorldLe w m (w.trunc h) m := by
  rw [World.trunc_self]; exact WorldLe.refl w m

/-- `WorldLe` transports to any truncation level. -/
theorem WorldLe.trunc {k j : Nat} (hjk : j ≤ k) {Ψ2 Ψ1 : World k} {m2 m1}
    (h : WorldLe Ψ2 m2 Ψ1 m1) : WorldLe (Ψ2.trunc hjk) m2 (Ψ1.trunc hjk) m1 := by
  refine ⟨h.1, fun l R hR => ?_⟩
  rw [World.trunc_lookup] at hR ⊢
  cases hΨ1 : Ψ1.lookup l with
  | none => rw [hΨ1] at hR; simp at hR
  | some R1 => rw [hΨ1] at hR; rw [h.2 l R1 hΨ1]; exact hR

end CC
