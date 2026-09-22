import Semantic.CC.Semantics
import Semantic.CC.TypeSystem
import Semantic.CC.Denotation.World
import Semantic.Prelude

/-!
# Denotations of types: the step-indexed Kripke model

Types are interpreted as predicates on expressions relative to a *Kripke world* `(k, st, m)`:
a step index `k`, a store typing `st : StoreTyping k` (the Ahmed world-parametrized store,
see `Denotation/World.lean`) and a memory `m`.  Shape types are additionally indexed by an
authority (the capability set the value may exercise), as in the original CC model.
-/

namespace CC

/-- Store typing at index `k`: maps locations to optional step-indexed relations. -/
abbrev StoreTyping (k : Nat) : Type := World k

/-- A step-indexed value relation stored at a cell. -/
abbrev MonRel (k : Nat) : Type := SemRel k

/-- Denotation of types at a fixed world. -/
def Denot := Memory -> Exp {} -> Prop

/-- An indexed denotation: a `Denot` parametrised by a step index `k` and a store typing
`st : StoreTyping k`. -/
def IDenot := (k : Nat) -> StoreTyping k -> Denot

/-- Indexed pre-denotation. It takes an authority to form an indexed denotation. -/
def IPreDenot := CapabilitySet -> IDenot

/-- Capture-denotation. Given any memory, it produces a set of capabilities. -/
def CapDenot := Memory -> CapabilitySet

/-- A bound on capability sets. It can either be a concrete set of the top element. -/
inductive CapabilityBound : Type where
| top : CapabilityBound
| set : CapabilitySet -> CapabilityBound

/-- Capture bound denotation. -/
def CapBoundDenot := Memory -> CapabilityBound

def Denot.is_monotonic (d : Denot) : Prop :=
  ∀ {m1 m2 : Memory} {e},
    m2.subsumes m1 ->
    d m1 e ->
    d m2 e

def CapDenot.is_monotonic_for (cd : CapDenot) (cs : CaptureSet {}) : Prop :=
  ∀ {m1 m2 : Memory},
    cs.WfInHeap m1.heap ->
    m2.subsumes m1 ->
    cd m1 = cd m2

def Denot.is_transparent (d : Denot) : Prop :=
  ∀ {m : Memory} {x : Nat} {v},
    m.lookup x = some (.val v) ->
    d m v.unwrap ->
    d m (.var (.free x))

def Denot.is_bool_independent (d : Denot) : Prop :=
  ∀ {m : Memory},
    d m .btrue <-> d m .bfalse

/-- For simple values, compute_reachability equals resolve_reachability. -/
theorem compute_reachability_eq_resolve_reachability
  (h : Heap) (v : Exp {}) (hv : v.IsSimpleVal) :
  compute_reachability h v hv = resolve_reachability h v := by
  cases hv <;> rfl

/-- Heap invariant: the reachability stored in a heap value equals the computed
    reachability for that value. -/
theorem Memory.reachability_invariant :
  ∀ (m : Memory) (x : Nat) (v : HeapVal),
    m.heap x = some (Cell.val v) ->
    v.reachability = compute_reachability m.heap v.unwrap v.isVal := fun m x v hx =>
  m.wf.wf_reach x v.unwrap v.isVal v.reachability hx

/-- Reachability of a heap location equals resolve_reachability of the stored value. -/
theorem reachability_of_loc_eq_resolve_reachability
  (m : Memory) (x : Nat) (v : HeapVal)
  (hx : m.heap x = some (Cell.val v)) :
  reachability_of_loc m.heap x = resolve_reachability m.heap v.unwrap := by
  unfold reachability_of_loc
  rw [hx]
  change v.reachability = resolve_reachability m.heap v.unwrap
  rw [Memory.reachability_invariant m x v hx]
  exact compute_reachability_eq_resolve_reachability m.heap v.unwrap v.isVal

/-! ## Properties of indexed denotations -/

/-- Subsumption-monotonicity at every fixed world. -/
def IDenot.is_monotonic (d : IDenot) : Prop :=
  ∀ k st, (d k st).is_monotonic

/-- Monotonicity along the typed future relation `WorldLe`. -/
def IDenot.worldle_monotonic (d : IDenot) : Prop :=
  ∀ {k : Nat} {st1 st2 : StoreTyping k} {m1 m2 e},
    WorldLe st2 m2 st1 m1 → d k st1 m1 e → d k st2 m2 e

/-- Downward closure in the step index, through world truncation. -/
def IDenot.is_downward_closed (d : IDenot) : Prop :=
  ∀ {j k : Nat} (hjk : j ≤ k) {st : StoreTyping k} {m e}, d k st m e → d j (st.trunc hjk) m e

def IDenot.is_transparent (d : IDenot) : Prop :=
  ∀ k st, (d k st).is_transparent

def IDenot.is_bool_independent (d : IDenot) : Prop :=
  ∀ k st, (d k st).is_bool_independent

/-- A proper indexed denotation. -/
def IDenot.is_proper (d : IDenot) : Prop :=
  d.is_monotonic
  ∧ d.is_transparent
  ∧ d.is_bool_independent
  ∧ d.worldle_monotonic
  ∧ d.is_downward_closed

/-- This pre-denotation actually enforces the reachability bound. -/
def IPreDenot.is_reachability_safe (pd : IPreDenot) : Prop :=
  ∀ R k st m e,
    pd R k st m e ->
    resolve_reachability m.heap e ⊆ R

/-- This pre-denotation is monotonic over authorities. -/
def IPreDenot.is_reachability_monotonic (pd : IPreDenot) : Prop :=
  ∀ R1 R2,
    R1 ⊆ R2 ->
    ∀ k st m e,
      pd R1 k st m e ->
      pd R2 k st m e

/-- This pre-denotation entails heap well-formedness. -/
def IPreDenot.implies_wf (pd : IPreDenot) : Prop :=
  ∀ R k st m e,
    pd R k st m e ->
    e.WfInHeap m.heap

/-- This pre-denotation is "tight" on authorities. -/
def IPreDenot.is_tight (pd : IPreDenot) : Prop :=
  ∀ R k st m fx,
    pd R k st m (.var (.free fx)) ->
    pd (reachability_of_loc m.heap fx) k st m (.var (.free fx))

/-- This is a proper pre-denotation. -/
def IPreDenot.is_proper (pd : IPreDenot) : Prop :=
  pd.is_reachability_safe
  ∧ pd.is_reachability_monotonic
  ∧ pd.implies_wf
  ∧ pd.is_tight
  ∧ ∀ C, (pd C).is_proper

def IPreDenot.is_monotonic (pd : IPreDenot) : Prop :=
  ∀ C, (pd C).is_monotonic

def IPreDenot.worldle_monotonic (pd : IPreDenot) : Prop :=
  ∀ C, (pd C).worldle_monotonic

def IPreDenot.is_downward_closed (pd : IPreDenot) : Prop :=
  ∀ C, (pd C).is_downward_closed

def IPreDenot.is_transparent (pd : IPreDenot) : Prop :=
  ∀ C, (pd C).is_transparent

def IPreDenot.is_bool_independent (pd : IPreDenot) : Prop :=
  ∀ C, (pd C).is_bool_independent

/-! ## Implication between indexed denotations -/

/-- `d1` implies `d2` at every future world above `(st, m)`, **index-uniformly**: at every
lower index `j ≤ k`, comparing against the base world truncated to that level. -/
def IDenot.ImplyAfter (d1 : IDenot) (k : Nat) (st : StoreTyping k) (m : Memory)
    (d2 : IDenot) : Prop :=
  ∀ (j : Nat) (hjk : j ≤ k) (st' : StoreTyping j) m',
    WorldLe st' m' (st.trunc hjk) m → ∀ e, d1 j st' m' e → d2 j st' m' e

def IPreDenot.ImplyAfter (pd1 : IPreDenot) (k : Nat) (st : StoreTyping k) (m : Memory)
    (pd2 : IPreDenot) : Prop :=
  ∀ C, (pd1 C).ImplyAfter k st m (pd2 C)

theorem IDenot.ImplyAfter.refl (d : IDenot) (k : Nat) (st : StoreTyping k) (m : Memory) :
    d.ImplyAfter k st m d :=
  fun _ _ _ _ _ _ h => h

theorem IDenot.ImplyAfter.trans {d1 d2 d3 : IDenot} {k : Nat} {st : StoreTyping k} {m : Memory}
    (h12 : d1.ImplyAfter k st m d2) (h23 : d2.ImplyAfter k st m d3) : d1.ImplyAfter k st m d3 :=
  fun j hjk st' m' hwle e h => h23 j hjk st' m' hwle e (h12 j hjk st' m' hwle e h)

/-- `ImplyAfter` weakens its base world along `subsumes`. -/
theorem IDenot.imply_after_subsumes {d1 d2 : IDenot} {k : Nat} {st : StoreTyping k}
    {m1 m2 : Memory} (himp : d1.ImplyAfter k st m1 d2) (hmem : m2.subsumes m1) :
    d1.ImplyAfter k st m2 d2 :=
  fun j hjk st' m' hwle e h =>
    himp j hjk st' m' (WorldLe.trans (WorldLe.of_subsumes hmem) hwle) e h

/-- `ImplyAfter` weakens its base world along `WorldLe`. -/
theorem IDenot.imply_after_worldle {d1 d2 : IDenot} {k : Nat} {st1 st2 : StoreTyping k}
    {m1 m2 : Memory} (himp : d1.ImplyAfter k st1 m1 d2) (hwle : WorldLe st2 m2 st1 m1) :
    d1.ImplyAfter k st2 m2 d2 :=
  fun j hjk st' m' hwle' e h =>
    himp j hjk st' m' (WorldLe.trans (WorldLe.trunc hjk hwle) hwle') e h

/-- `ImplyAfter` descends through world truncation. -/
theorem IDenot.ImplyAfter.trunc {d1 d2 : IDenot} {j k : Nat} (hjk : j ≤ k)
    {st : StoreTyping k} {m : Memory} (himp : d1.ImplyAfter k st m d2) :
    d1.ImplyAfter j (st.trunc hjk) m d2 :=
  fun i hij st' m' hwle e h =>
    himp i (Nat.le_trans hij hjk) st' m'
      (by rw [World.trunc_trunc] at hwle; exact hwle) e h

/-- Apply an `ImplyAfter` at its base world. -/
theorem IDenot.imply_after_apply {d1 d2 : IDenot} {k : Nat} {st : StoreTyping k} {m : Memory}
    (himp : d1.ImplyAfter k st m d2) {e : Exp {}} (h : d1 k st m e) : d2 k st m e :=
  himp k (Nat.le_refl k) st m (WorldLe.refl_trunc_self _ st m) e h

theorem IPreDenot.ImplyAfter.refl (pd : IPreDenot) (k : Nat) (st : StoreTyping k) (m : Memory) :
    pd.ImplyAfter k st m pd :=
  fun C => IDenot.ImplyAfter.refl (pd C) k st m

theorem IPreDenot.ImplyAfter.trans {pd1 pd2 pd3 : IPreDenot} {k : Nat} {st : StoreTyping k}
    {m : Memory} (h12 : pd1.ImplyAfter k st m pd2) (h23 : pd2.ImplyAfter k st m pd3) :
    pd1.ImplyAfter k st m pd3 :=
  fun C => IDenot.ImplyAfter.trans (h12 C) (h23 C)

theorem IPreDenot.imply_after_subsumes {pd1 pd2 : IPreDenot} {k : Nat} {st : StoreTyping k}
    {m1 m2 : Memory} (himp : pd1.ImplyAfter k st m1 pd2) (hmem : m2.subsumes m1) :
    pd1.ImplyAfter k st m2 pd2 :=
  fun C => IDenot.imply_after_subsumes (himp C) hmem

theorem IPreDenot.imply_after_worldle {pd1 pd2 : IPreDenot} {k : Nat} {st1 st2 : StoreTyping k}
    {m1 m2 : Memory} (himp : pd1.ImplyAfter k st1 m1 pd2) (hwle : WorldLe st2 m2 st1 m1) :
    pd1.ImplyAfter k st2 m2 pd2 :=
  fun C => IDenot.imply_after_worldle (himp C) hwle

theorem IPreDenot.ImplyAfter.trunc {pd1 pd2 : IPreDenot} {j k : Nat} (hjk : j ≤ k)
    {st : StoreTyping k} {m : Memory} (himp : pd1.ImplyAfter k st m pd2) :
    pd1.ImplyAfter j (st.trunc hjk) m pd2 :=
  fun C => IDenot.ImplyAfter.trunc hjk (himp C)

/-! ## Type environments -/

inductive TypeInfo : Kind -> Type where
| var : Nat -> TypeInfo .var
| tvar : IPreDenot -> TypeInfo .tvar
| cvar : CaptureSet {} -> TypeInfo .cvar

inductive TypeEnv : Sig -> Type where
| empty : TypeEnv {}
| extend :
  TypeEnv s ->
  TypeInfo k ->
  TypeEnv (s,,k)

def TypeEnv.extend_var (Γ : TypeEnv s) (x : Nat) : TypeEnv (s,x) :=
  Γ.extend (.var x)

def TypeEnv.extend_tvar (Γ : TypeEnv s) (T : IPreDenot) : TypeEnv (s,X) :=
  Γ.extend (.tvar T)

def TypeEnv.extend_cvar
  (Γ : TypeEnv s) (ground : CaptureSet {}) :
  TypeEnv (s,C) :=
  Γ.extend (.cvar ground)

def TypeEnv.lookup : (Γ : TypeEnv s) -> (x : BVar s k) -> TypeInfo k
| .extend _ info, .here => info
| .extend Γ _,    .there x => Γ.lookup x

def TypeEnv.lookup_var (Γ : TypeEnv s) (x : BVar s .var) : Nat :=
  match Γ.lookup x with
  | .var y => y

def TypeEnv.lookup_tvar (Γ : TypeEnv s) (x : BVar s .tvar) : IPreDenot :=
  match Γ.lookup x with
  | .tvar T => T

def TypeEnv.lookup_cvar (Γ : TypeEnv s) (x : BVar s .cvar) : CaptureSet {} :=
  match Γ.lookup x with
  | .cvar cs => cs

def Subst.from_TypeEnv (env : TypeEnv s) : Subst s {} where
  var := fun x => .free (env.lookup_var x)
  tvar := fun _ => .top
  cvar := fun c => env.lookup_cvar c

theorem Subst.from_TypeEnv_empty :
  Subst.from_TypeEnv TypeEnv.empty = Subst.id := by
  apply Subst.funext
  · intro x; cases x
  · intro X; cases X
  · intro C; cases C

/-- Compute denotation for a ground capture set. -/
def CaptureSet.ground_denot : CaptureSet {} -> CapDenot
| .empty => fun _ => {}
| .union cs1 cs2 => fun m =>
  (cs1.ground_denot m) ∪ (cs2.ground_denot m)
| .var (.free x) => fun m => reachability_of_loc m.heap x

def CaptureSet.denot (ρ : TypeEnv s) (cs : CaptureSet s) : CapDenot :=
  (cs.subst (Subst.from_TypeEnv ρ)).ground_denot

def CaptureBound.denot : TypeEnv s -> CaptureBound s -> CapBoundDenot
| _, .unbound => fun _ => .top
| env, .bound cs => fun m => .set (cs.denot env m)

inductive CapabilitySet.BoundedBy : CapabilitySet -> CapabilityBound -> Prop where
| top :
  CapabilitySet.BoundedBy C CapabilityBound.top
| set :
  C1 ⊆ C2 ->
  CapabilitySet.BoundedBy C1 (CapabilityBound.set C2)

inductive CapabilityBound.SubsetEq : CapabilityBound -> CapabilityBound -> Prop where
| refl :
  CapabilityBound.SubsetEq B B
| set :
  C1 ⊆ C2 ->
  CapabilityBound.SubsetEq (CapabilityBound.set C1) (CapabilityBound.set C2)
| top :
  CapabilityBound.SubsetEq B CapabilityBound.top

instance : HasSubset CapabilityBound where
  Subset := CapabilityBound.SubsetEq

theorem CapabilitySet.BoundedBy.trans
  {C : CapabilitySet} {B1 B2 : CapabilityBound}
  (hbound : CapabilitySet.BoundedBy C B1)
  (hsub : B1 ⊆ B2) :
  CapabilitySet.BoundedBy C B2 := by
  cases hsub with
  | refl => exact hbound
  | set hsub_set =>
    cases hbound with
    | set hbound_set =>
      exact CapabilitySet.BoundedBy.set
        (CapabilitySet.Subset.trans hbound_set hsub_set)
  | top => exact CapabilitySet.BoundedBy.top

/-! ## Well-typed worlds -/

/-- **Store consistency**: every store-typed location is an allocated mutable cell. -/
def StoreConsistent {k : Nat} (st : StoreTyping k) (m : Memory) : Prop :=
  ∀ l R, st.lookup l = some R → ∃ n, m.lookup l = some (.capability (.mcell n))

/-- A memory is **well-typed** for store typing `st : StoreTyping k`: store-consistent,
every stored relation is growth-stable, and every `st`-typed cell holds a value satisfying
its stored relation at every lower level `i < k` (at the truncated world). -/
def MemTyped (k : Nat) (st : StoreTyping k) (m : Memory) : Prop :=
  StoreConsistent st m ∧
  (∀ l (R : MonRel k), st.lookup l = some R →
    ∀ (i : Fin k) (w1 w2 : StoreTyping i.val) (m1 m2 : Memory),
      WorldLe w2 m2 w1 m1 → ∀ e, R i w1 m1 e → R i w2 m2 e) ∧
  ∀ l n (R : MonRel k), st.lookup l = some R → m.lookup l = some (.capability (.mcell n)) →
    ∀ (i : Fin k), R i (st.trunc (Nat.le_of_lt i.isLt)) m (.var (.free n))

/-- `MemTyped` descends through world truncation. -/
theorem MemTyped_trunc {j k : Nat} (hjk : j ≤ k) {st : StoreTyping k} {m : Memory}
    (h : MemTyped k st m) : MemTyped j (st.trunc hjk) m := by
  obtain ⟨hcons, hstable, hgood⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro l R' hl
    rw [World.trunc_lookup] at hl
    cases hlk : st.lookup l with
    | none => rw [hlk] at hl; cases hl
    | some R0 => exact hcons l R0 hlk
  · intro l R' hl i w1 w2 m1 m2 hw e hR'
    rw [World.trunc_lookup] at hl
    cases hlk : st.lookup l with
    | none => rw [hlk] at hl; cases hl
    | some R0 =>
      rw [hlk, Option.map_some] at hl
      injection hl with hl; subst hl
      exact hstable l R0 hlk ⟨i.val, Nat.lt_of_lt_of_le i.isLt hjk⟩ w1 w2 m1 m2 hw e hR'
  · intro l n R' hl hlkm i
    rw [World.trunc_lookup] at hl
    cases hlk : st.lookup l with
    | none => rw [hlk] at hl; cases hl
    | some R0 =>
      rw [hlk, Option.map_some] at hl
      injection hl with hl; subst hl
      rw [World.trunc_trunc]
      exact hgood l n R0 hlk hlkm ⟨i.val, Nat.lt_of_lt_of_le i.isLt hjk⟩

/-- The empty store typing types any memory. -/
theorem MemTyped_empty (k : Nat) (m : Memory) : MemTyped k (World.empty k) m := by
  refine ⟨?_, ?_, ?_⟩
  · intro l R h; rw [World.empty_lookup] at h; cases h
  · intro l R h; rw [World.empty_lookup] at h; cases h
  · intro l n R h; rw [World.empty_lookup] at h; cases h

/-! ## Expression denotations -/

/-- **Pack-witness bound**: if the answer is a pack, every location reachable from its
witness is either in the authority `R` or was allocated by the run (trace `t`). -/
def pack_bound (R : CapabilitySet) (t : Trace) (v : Exp {}) (m' : Memory) : Prop :=
  ∀ cs fx, v = .pack cs (.free fx) →
    reachability_of_loc m'.heap fx ⊆ R ∪ CapabilitySet.ofList t.allocList

/-- The budget-guarded postcondition of the expression relation: for runs within budget,
the result lands at a well-typed future world at the decremented index and satisfies the
indexed value denotation `D` there. -/
def ExpPost (k : Nat) (st : StoreTyping k) (m : Memory) (R : CapabilitySet) (D : IDenot) :
    Tpost :=
  fun t v m' =>
    t.readCount < k →
    ∃ (st' : StoreTyping (k - t.readCount)),
      WorldLe st' m' (st.trunc (Nat.sub_le k t.readCount)) m ∧
      MemTyped (k - t.readCount) st' m' ∧
      D (k - t.readCount) st' m' v ∧
      pack_bound R t v m'

/-- The expression relation for an indexed value denotation `D`: assuming the starting
world is well-typed, the expression is safe for `k` reads within authority `R`, and every
within-budget run satisfies `ExpPost`. -/
def ExpDenot (D : IDenot) (R : CapabilitySet) (k : Nat) (st : StoreTyping k) (m : Memory)
    (e : Exp {}) : Prop :=
  MemTyped k st m → Eval k R m e (ExpPost k st m R D)

mutual

def Ty.shape_val_denot : TypeEnv s -> Ty .shape s -> IPreDenot
| _, .top => fun R _ _ m e =>
  e.WfInHeap m.heap ∧ resolve_reachability m.heap e ⊆ R
| env, .tvar X => env.lookup_tvar X
| _, .unit => fun _ _ _ m e => resolve m.heap e = some .unit
| _, .cap => fun A _ _ m e =>
  e.WfInHeap m.heap ∧
  ∃ label : Nat,
    e = .var (.free label) ∧
    m.lookup label = some (.capability .basic) ∧
    label ∈ A
| _, .bool => fun _ _ _ m e =>
  resolve m.heap e = some .btrue ∨ resolve m.heap e = some .bfalse
| env, .cell T => fun R k st m e =>
  ∃ (l n0 : Nat) (Rl : MonRel k),
    e = .var (.free l) ∧
    m.lookup l = some (.capability (.mcell n0)) ∧
    l ∈ R ∧
    st.lookup l = some Rl ∧
    (∀ (j : Fin k) (w' : StoreTyping j.val) (m' : Memory) (e' : Exp {}),
      Rl j w' m' e' ↔ Ty.capt_val_denot env T j.val w' m' e')
| env, .arrow T1 T2 => fun A k st m e =>
  e.WfInHeap m.heap ∧
  ∃ cs T0 t0,
    resolve m.heap e = some (.abs cs T0 t0) ∧
    cs.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs
    R0 ⊆ A ∧
    (∀ (j : Nat) (hjk : j ≤ k) (st' : StoreTyping j) (m' : Memory) (arg : Nat),
      WorldLe st' m' (st.trunc hjk) m ->
      Ty.capt_val_denot env T1 j st' m' (.var (.free arg)) ->
      ExpDenot (Ty.exi_val_denot (env.extend_var arg) T2)
        (R0 ∪ (reachability_of_loc m'.heap arg)) j st' m'
        (t0.subst (Subst.openVar (.free arg))))
| env, .poly T1 T2 => fun A k st m e =>
  e.WfInHeap m.heap ∧
  ∃ cs S0 t0,
    resolve m.heap e = some (.tabs cs S0 t0) ∧
    cs.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs
    R0 ⊆ A ∧
    (∀ (j : Nat) (hjk : j ≤ k) (st' : StoreTyping j) (m' : Memory) (denot : IPreDenot),
      WorldLe st' m' (st.trunc hjk) m ->
      denot.is_proper ->
      denot.ImplyAfter j st' m' (Ty.shape_val_denot env T1) ->
      ExpDenot (Ty.exi_val_denot (env.extend_tvar denot) T2) R0 j st' m'
        (t0.subst (Subst.openTVar .top)))
| env, .cpoly B T => fun A k st m e =>
  e.WfInHeap m.heap ∧
  ∃ cs B0 t0,
    resolve m.heap e = some (.cabs cs B0 t0) ∧
    cs.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs
    R0 ⊆ A ∧
    (∀ (j : Nat) (hjk : j ≤ k) (st' : StoreTyping j) (m' : Memory) (CS : CaptureSet {}),
      CS.WfInHeap m'.heap ->
      WorldLe st' m' (st.trunc hjk) m ->
      ((CS.denot TypeEnv.empty m').BoundedBy (B.denot env m')) ->
      ExpDenot (Ty.exi_val_denot (env.extend_cvar CS) T) R0 j st' m'
        (t0.subst (Subst.openCVar CS)))

def Ty.capt_val_denot : TypeEnv s -> Ty .capt s -> IDenot
| ρ, .capt C S => fun k st mem exp =>
  exp.IsSimpleAns ∧
  exp.WfInHeap mem.heap ∧
  (C.subst (Subst.from_TypeEnv ρ)).WfInHeap mem.heap ∧
  Ty.shape_val_denot ρ S (C.denot ρ mem) k st mem exp

def Ty.exi_val_denot : TypeEnv s -> Ty .exi s -> IDenot
| ρ, .typ T => Ty.capt_val_denot ρ T
| ρ, .exi T => fun k st m e =>
  ∃ (CS : CaptureSet {}) (x : Var .var {}),
    resolve m.heap e = some (.pack CS x) ∧
    CS.WfInHeap m.heap ∧
    Ty.capt_val_denot (ρ.extend_cvar CS) T k st m (.var x)

end

/-- Expression denotation for capturing types. -/
def Ty.capt_exp_denot (ρ : TypeEnv s) (T : Ty .capt s) : IPreDenot :=
  ExpDenot (Ty.capt_val_denot ρ T)

/-- Expression denotation for existential types. -/
def Ty.exi_exp_denot (ρ : TypeEnv s) (E : Ty .exi s) : IPreDenot :=
  ExpDenot (Ty.exi_val_denot ρ E)

@[simp]
instance instCaptHasDenotation :
  HasDenotation (Ty .capt s) (TypeEnv s) IDenot where
  interp := Ty.capt_val_denot

@[simp]
instance instCaptHasExpDenotation :
  HasExpDenotation (Ty .capt s) (TypeEnv s) IPreDenot where
  interp := Ty.capt_exp_denot

@[simp]
instance instExiHasDenotation :
  HasDenotation (Ty .exi s) (TypeEnv s) IDenot where
  interp := Ty.exi_val_denot

@[simp]
instance instExiHasExpDenotation :
  HasExpDenotation (Ty .exi s) (TypeEnv s) IPreDenot where
  interp := Ty.exi_exp_denot

@[simp]
instance instShapeHasDenotation :
  HasDenotation (Ty .shape s) (TypeEnv s) IPreDenot where
  interp := Ty.shape_val_denot

@[simp]
instance instCaptureSetHasDenotation :
  HasDenotation (CaptureSet s) (TypeEnv s) CapDenot where
  interp := CaptureSet.denot

@[simp]
instance instCaptureBoundHasDenotation :
  HasDenotation (CaptureBound s) (TypeEnv s) CapBoundDenot where
  interp := CaptureBound.denot

/-- Unfolding lemma for capturing-type denotation. -/
theorem capt_val_denot_capt
  (env : TypeEnv s) (C : CaptureSet s) (S : Ty .shape s) :
    Ty.capt_val_denot env (Ty.capt C S) = fun k st mem exp =>
    exp.IsSimpleAns ∧
    exp.WfInHeap mem.heap ∧
    (C.subst (Subst.from_TypeEnv env)).WfInHeap mem.heap ∧
    Ty.shape_val_denot env S (C.denot env mem) k st mem exp := by
  exact Ty.capt_val_denot.eq_1 env C S

/-- Unfolding lemma for existential-type val denotation (typ case). -/
theorem exi_val_denot_typ
  (env : TypeEnv s) (T : Ty .capt s) :
    Ty.exi_val_denot env (Ty.typ T) = Ty.capt_val_denot env T := by
  exact Ty.exi_val_denot.eq_1 env T

def EnvTyping : Ctx s -> TypeEnv s -> (k : Nat) -> StoreTyping k -> Memory -> Prop
| .empty, .empty, _, _, _ => True
| .push Γ (.var T), .extend env (.var n), k, st, m =>
  Ty.capt_val_denot env T k st m (.var (.free n)) ∧
  EnvTyping Γ env k st m
| .push Γ (.tvar S), .extend env (.tvar denot), k, st, m =>
  denot.is_proper ∧
  denot.ImplyAfter k st m (Ty.shape_val_denot env S) ∧
  EnvTyping Γ env k st m
| .push Γ (.cvar B), .extend env (.cvar cs), k, st, m =>
  (cs.WfInHeap m.heap) ∧
  ((B.subst (Subst.from_TypeEnv env)).WfInHeap m.heap) ∧
  ((cs.ground_denot m).BoundedBy (B.denot env m)) ∧
  EnvTyping Γ env k st m

def SemanticTyping (C : CaptureSet s) (Γ : Ctx s) (e : Exp s) (E : Ty .exi s) : Prop :=
  ∀ ρ k st m,
    EnvTyping Γ ρ k st m ->
    Ty.exi_exp_denot ρ E (C.denot ρ m) k st m (e.subst (Subst.from_TypeEnv ρ))

notation:65 C " # " Γ " ⊨ " e " : " T => SemanticTyping C Γ e T


theorem Subst.from_TypeEnv_weaken_open {s : Sig} {env : TypeEnv s} {n : Nat} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openVar (.free n)) =
    Subst.from_TypeEnv (env.extend_var n) := by
  apply Subst.funext
  · intro y
    cases y <;> rfl
  · intro X
    cases X
    rfl
  · intro C
    cases C with
    | there C' =>
      simp only [Subst.from_TypeEnv, Subst.lift, Subst.comp, Subst.openVar,
        TypeEnv.extend_var, TypeEnv.lookup_cvar]
      exact CaptureSet.weaken_openVar

theorem Exp.from_TypeEnv_weaken_open {s : Sig} {env : TypeEnv s} {n : Nat}
    {e : Exp (Sig.extend_var s)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free n)) =
    e.subst (Subst.from_TypeEnv (env.extend_var n)) := by
  rw [Exp.subst_comp]
  exact congrArg _ Subst.from_TypeEnv_weaken_open

theorem Subst.from_TypeEnv_weaken_open_tvar {env : TypeEnv s} {d : IPreDenot} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openTVar .top) =
    Subst.from_TypeEnv (env.extend_tvar d) := by
  apply Subst.funext
  · intro x
    cases x
    rfl
  · intro X
    cases X
    case here => rfl
    case there X' =>
      simp [Subst.comp, Subst.lift, Subst.from_TypeEnv, Subst.openTVar,
        TypeEnv.extend_tvar, Ty.subst, Ty.rename]
  · intro C
    cases C with
    | there C' =>
      simp only [Subst.from_TypeEnv, Subst.lift, Subst.comp, Subst.openTVar,
        TypeEnv.extend_tvar, TypeEnv.lookup_cvar]
      exact CaptureSet.weaken_openTVar

theorem Exp.from_TypeEnv_weaken_open_tvar
  {env : TypeEnv s} {d : IPreDenot} {e : Exp (s,X)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openTVar .top) =
    e.subst (Subst.from_TypeEnv (env.extend_tvar d)) := by
  rw [Exp.subst_comp]
  exact congrArg _ Subst.from_TypeEnv_weaken_open_tvar

theorem Subst.from_TypeEnv_weaken_open_cvar
  {env : TypeEnv s} {cs : CaptureSet {}} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openCVar cs) =
    Subst.from_TypeEnv (env.extend_cvar cs) := by
  apply Subst.funext
  · intro x
    cases x
    rfl
  · intro X
    cases X
    rfl
  · intro C
    cases C
    case here => rfl
    case there C' =>
      simp only [Subst.comp, Subst.lift, Subst.from_TypeEnv, Subst.openCVar,
        TypeEnv.extend_cvar, TypeEnv.lookup_cvar]
      exact CaptureSet.weaken_openCVar

theorem Exp.from_TypeEnv_weaken_open_cvar
  {env : TypeEnv s} {cs : CaptureSet {}} {e : Exp (s,C)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openCVar cs) =
    e.subst (Subst.from_TypeEnv (env.extend_cvar cs)) := by
  rw [Exp.subst_comp]
  exact congrArg _ Subst.from_TypeEnv_weaken_open_cvar

theorem Subst.from_TypeEnv_weaken_unpack :
  (Subst.from_TypeEnv ρ).lift.lift.comp (Subst.unpack cs (.free x)) =
    Subst.from_TypeEnv ((ρ.extend_cvar cs).extend_var x) := by
  apply Subst.funext
  · intro y
    cases y
    case here => rfl
    case there y' =>
      cases y'
      case there v =>
        simp only [Subst.comp, Subst.unpack, Var.subst]
        rw [Subst.lift_there_var_eq]
        rw [Subst.lift_there_var_eq]
        simp [Subst.from_TypeEnv, Var.rename, TypeEnv.lookup_var]
        rfl
  · intro X
    cases X
    case there X' =>
      cases X'
      case there X0 => rfl
  · intro c
    cases c
    case there c' =>
      cases c'
      case here =>
        simp only [Subst.comp, Subst.unpack]
        rw [Subst.lift_there_cvar_eq]
        simp [Subst.lift, CaptureSet.subst, CaptureSet.rename]
        rfl
      case there c0 =>
        have helper : ∀ (g : CaptureSet {}),
            ((g.rename Rename.succ).rename Rename.succ).subst
              (Subst.unpack cs (.free x)) = g := by
          intro g
          induction g with
          | empty => rfl
          | union g1 g2 ih1 ih2 =>
            show CaptureSet.subst _ _ = _
            simp only [CaptureSet.rename, CaptureSet.subst]
            rw [ih1, ih2]
          | var v =>
            cases v with
            | bound bv => cases bv
            | free n => rfl
          | cvar cv => cases cv
        change CaptureSet.subst (CaptureSet.rename (CaptureSet.rename (ρ.lookup_cvar c0)
          Rename.succ) Rename.succ) (Subst.unpack cs (.free x)) = _
        rw [helper (ρ.lookup_cvar c0)]
        rfl

/-- If a TypeEnv is typed with EnvTyping, then the substitution obtained from it
via `Subst.from_TypeEnv` is well-formed in the heap. -/
theorem from_TypeEnv_wf_in_heap
  {Γ : Ctx s} {ρ : TypeEnv s} {k : Nat} {st : StoreTyping k} {m : Memory}
  (htyping : EnvTyping Γ ρ k st m) :
  (Subst.from_TypeEnv ρ).WfInHeap m.heap := by
  induction Γ with
  | empty =>
    cases ρ with
    | empty =>
      constructor
      · intro x; cases x
      · intro X; cases X
      · intro C; cases C
  | push Γ' b ih =>
    cases ρ with
    | extend ρ' info =>
      cases b with
      | var T =>
        cases info with
        | var n =>
          unfold EnvTyping at htyping
          have ⟨htype, htyping'⟩ := htyping
          cases T with
          | capt C S =>
            rw [capt_val_denot_capt] at htype
            have ⟨_, hwf, _, _⟩ := htype
            cases hwf with
            | wf_var hwf_var =>
              have ih_wf := ih htyping'
              constructor
              · intro x
                cases x with
                | here => exact hwf_var
                | there x' => exact ih_wf.wf_var x'
              · intro X
                cases X with
                | there X' => exact ih_wf.wf_tvar X'
              · intro C_var
                cases C_var with
                | there C' => exact ih_wf.wf_cvar C'
      | tvar S =>
        cases info with
        | tvar denot =>
          unfold EnvTyping at htyping
          have ⟨_, _, htyping'⟩ := htyping
          have ih_wf := ih htyping'
          constructor
          · intro x
            cases x with
            | there x' =>
              simp only [Subst.from_TypeEnv, TypeEnv.lookup_var, TypeEnv.lookup]
              exact ih_wf.wf_var x'
          · intro X
            cases X with
            | here =>
              simp only [Subst.from_TypeEnv]; exact .wf_top
            | there X' =>
              simp only [Subst.from_TypeEnv]
              exact ih_wf.wf_tvar X'
          · intro C_var
            cases C_var with
            | there C' =>
              simp only [Subst.from_TypeEnv]
              exact ih_wf.wf_cvar C'
      | cvar B =>
        cases info with
        | cvar cs =>
          unfold EnvTyping at htyping
          have ⟨hwf, hwf_bound, hsub, htyping'⟩ := htyping
          have ih_wf := ih htyping'
          constructor
          · intro x
            cases x with
            | there x' =>
              simp only [Subst.from_TypeEnv, TypeEnv.lookup_var, TypeEnv.lookup]
              exact ih_wf.wf_var x'
          · intro X
            cases X with
            | there X' =>
              simp only [Subst.from_TypeEnv]
              exact ih_wf.wf_tvar X'
          · intro C_var
            cases C_var with
            | here =>
              simp only [Subst.from_TypeEnv, TypeEnv.lookup_cvar, TypeEnv.lookup]
              exact hwf
            | there C' =>
              simp only [Subst.from_TypeEnv]
              exact ih_wf.wf_cvar C'

/-! ## Equivalence of denotations -/

def IDenot.Equiv (d1 d2 : IDenot) : Prop :=
  ∀ k st m e, (d1 k st m e) ↔ (d2 k st m e)

instance IDenot.instHasEquiv : HasEquiv IDenot where
  Equiv := IDenot.Equiv

theorem IDenot.equiv_def {d1 d2 : IDenot} :
  d1 ≈ d2 ↔ ∀ k st m e, (d1 k st m e) ↔ (d2 k st m e) := Iff.rfl

theorem IDenot.equiv_refl (d : IDenot) : d ≈ d := fun _ _ _ _ => Iff.rfl

theorem IDenot.eq_to_equiv {d1 d2 : IDenot} (h : d1 = d2) : d1 ≈ d2 := by
  subst h; exact IDenot.equiv_refl _

theorem IDenot.equiv_symm {d1 d2 : IDenot} (h : d1 ≈ d2) : d2 ≈ d1 :=
  fun k st m e => (h k st m e).symm

theorem IDenot.equiv_trans {d1 d2 d3 : IDenot} (h12 : d1 ≈ d2) (h23 : d2 ≈ d3) : d1 ≈ d3 :=
  fun k st m e => (h12 k st m e).trans (h23 k st m e)

theorem IDenot.equiv_ltr {d1 d2 : IDenot} {k st m e}
  (heqv : d1 ≈ d2) (h1 : d1 k st m e) : d2 k st m e :=
  (heqv k st m e).mp h1

theorem IDenot.equiv_rtl {d1 d2 : IDenot} {k st m e}
  (heqv : d1 ≈ d2) (h2 : d2 k st m e) : d1 k st m e :=
  (heqv k st m e).mpr h2

theorem IDenot.equiv_to_imply_after {d1 d2 : IDenot} (heqv : d1 ≈ d2)
  (k : Nat) (st : StoreTyping k) (m : Memory) : d1.ImplyAfter k st m d2 :=
  fun j _ st' m' _ e h => (heqv j st' m' e).mp h

def IPreDenot.Equiv (pd1 pd2 : IPreDenot) : Prop :=
  ∀ A, (pd1 A) ≈ (pd2 A)

instance IPreDenot.instHasEquiv : HasEquiv IPreDenot where
  Equiv := IPreDenot.Equiv

theorem IPreDenot.equiv_def {pd1 pd2 : IPreDenot} :
  pd1 ≈ pd2 ↔ ∀ A k st m e, (pd1 A k st m e) ↔ (pd2 A k st m e) :=
  ⟨fun h A k st m e => (h A) k st m e, fun h A k st m e => h A k st m e⟩

theorem IPreDenot.eq_to_equiv {pd1 pd2 : IPreDenot} (h : pd1 = pd2) : pd1 ≈ pd2 := by
  subst h; exact fun A => IDenot.equiv_refl _

theorem IPreDenot.equiv_refl (pd : IPreDenot) : pd ≈ pd :=
  fun A => IDenot.equiv_refl (pd A)

theorem IPreDenot.equiv_symm (pd1 pd2 : IPreDenot) : pd1 ≈ pd2 -> pd2 ≈ pd1 := by
  intro h A; exact IDenot.equiv_symm (h A)

theorem IPreDenot.equiv_trans (pd1 pd2 pd3 : IPreDenot) :
    pd1 ≈ pd2 -> pd2 ≈ pd3 -> pd1 ≈ pd3 :=
  fun h12 h23 A => IDenot.equiv_trans (h12 A) (h23 A)

theorem IPreDenot.equiv_ltr {pd1 pd2 : IPreDenot} {A k st m e}
  (heqv : pd1 ≈ pd2) (h1 : pd1 A k st m e) : pd2 A k st m e :=
  (heqv A k st m e).mp h1

theorem IPreDenot.equiv_rtl {pd1 pd2 : IPreDenot} {A k st m e}
  (heqv : pd1 ≈ pd2) (h2 : pd2 A k st m e) : pd1 A k st m e :=
  (heqv A k st m e).mpr h2

/-! ## Resolution lemmas -/

theorem resolve_var_heap_some
  (hheap : heap x = some (.val v)) :
  resolve heap (.var (.free x)) = some v.unwrap := by
  simp [resolve, hheap]

theorem resolve_val
  (hval : v.IsVal) :
  resolve heap v = some v := by
  cases hval <;> rfl

theorem resolve_var_heap_trans
  (hheap : heap x = some (.val v)) :
  resolve heap (.var (.free x)) = resolve heap (v.unwrap) := by
  rw [resolve_var_heap_some hheap]
  rw [resolve_val v.isVal.to_IsVal]

theorem resolve_var_or_val
  (hv : resolve store e = some v) :
  (∃ x, e = .var x) ∨ e = v := by
  cases e
  all_goals try (solve | aesop | simp [resolve] at hv; aesop)

theorem resolve_ans_to_val
  (hv : resolve store e = some v)
  (hans : v.IsAns) :
  e.IsAns := by
  cases (resolve_var_or_val hv)
  case inl h =>
    have ⟨x, h⟩ := h
    rw [h]; exact .is_var
  case inr h => aesop

/-! ## Properties of type environments -/

structure TypeEnv.IsMonotonic (env : TypeEnv s) : Prop where
  tvar : ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_monotonic
  tvar_worldle : ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).worldle_monotonic

def TypeEnv.is_downward_closed (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_downward_closed

def TypeEnv.is_transparent (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_transparent

def TypeEnv.is_bool_independent (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_bool_independent

def TypeEnv.is_reachability_safe (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_reachability_safe

def TypeEnv.is_reachability_monotonic (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_reachability_monotonic

def TypeEnv.is_implying_wf (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).implies_wf

def TypeEnv.is_tight (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_tight

/-- All type variables of a typed environment carry proper pre-denotations. -/
theorem typed_env_tvar_is_proper
  (ht : EnvTyping Γ env k st mem) :
  ∀ X, (env.lookup_tvar X).is_proper := by
  induction Γ with
  | empty =>
    cases env with
    | empty => intro X; cases X
  | push Γ b ih =>
    cases env with
    | extend env' info =>
      cases b with
      | var T =>
        cases info with
        | var n =>
          simp only [EnvTyping] at ht
          have ⟨_, ht'⟩ := ht
          have ih_result := ih ht'
          intro X; cases X with
          | there X => simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]; exact ih_result X
      | tvar S =>
        cases info with
        | tvar d =>
          simp only [EnvTyping] at ht
          have ⟨hproper, _, ht'⟩ := ht
          have ih_result := ih ht'
          intro X; cases X with
          | here => simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]; exact hproper
          | there X => simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]; exact ih_result X
      | cvar B =>
        cases info with
        | cvar cs =>
          simp only [EnvTyping] at ht
          have ⟨_, _, _, ht'⟩ := ht
          have ih_result := ih ht'
          intro X; cases X with
          | there X => simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]; exact ih_result X

theorem typed_env_is_monotonic
  (ht : EnvTyping Γ env k st mem) :
  env.IsMonotonic := by
  have hprop := typed_env_tvar_is_proper ht
  constructor
  · intro X C
    exact (hprop X).2.2.2.2 C |>.1
  · intro X C
    exact (hprop X).2.2.2.2 C |>.2.2.2.1

theorem typed_env_is_downward_closed
  (ht : EnvTyping Γ env k st mem) :
  env.is_downward_closed := by
  have hprop := typed_env_tvar_is_proper ht
  intro X C
  exact (hprop X).2.2.2.2 C |>.2.2.2.2

theorem typed_env_is_transparent
  (ht : EnvTyping Γ env k st mem) :
  env.is_transparent := by
  have hprop := typed_env_tvar_is_proper ht
  intro X C
  exact (hprop X).2.2.2.2 C |>.2.1

theorem typed_env_is_bool_independent
  (ht : EnvTyping Γ env k st mem) :
  env.is_bool_independent := by
  have hprop := typed_env_tvar_is_proper ht
  intro X C
  exact (hprop X).2.2.2.2 C |>.2.2.1

theorem typed_env_is_reachability_safe
  (ht : EnvTyping Γ env k st mem) :
  env.is_reachability_safe := by
  have hprop := typed_env_tvar_is_proper ht
  intro X
  exact (hprop X).1

theorem typed_env_is_reachability_monotonic
  (ht : EnvTyping Γ env k st mem) :
  env.is_reachability_monotonic := by
  have hprop := typed_env_tvar_is_proper ht
  intro X
  exact (hprop X).2.1

theorem typed_env_is_implying_wf
  (ht : EnvTyping Γ env k st mem) :
  env.is_implying_wf := by
  have hprop := typed_env_tvar_is_proper ht
  intro X
  exact (hprop X).2.2.1

theorem typed_env_is_tight
  (ht : EnvTyping Γ env k st mem) :
  env.is_tight := by
  have hprop := typed_env_tvar_is_proper ht
  intro X
  exact (hprop X).2.2.2.1

/-- Extending an environment with a capture variable preserves the type-variable
properties (the type variables are unchanged). -/
theorem TypeEnv.extend_cvar_lookup_tvar (env : TypeEnv s) (cs : CaptureSet {})
    (X : BVar (s,C) .tvar) : ∃ X0, (env.extend_cvar cs).lookup_tvar X = env.lookup_tvar X0 := by
  cases X with
  | there X0 => exact ⟨X0, rfl⟩

theorem TypeEnv.IsMonotonic.extend_cvar {env : TypeEnv s} (h : env.IsMonotonic)
    (cs : CaptureSet {}) : (env.extend_cvar cs).IsMonotonic := by
  constructor
  · intro X
    obtain ⟨X0, hX0⟩ := TypeEnv.extend_cvar_lookup_tvar env cs X
    rw [hX0]; exact h.tvar X0
  · intro X
    obtain ⟨X0, hX0⟩ := TypeEnv.extend_cvar_lookup_tvar env cs X
    rw [hX0]; exact h.tvar_worldle X0

theorem TypeEnv.is_downward_closed.extend_cvar {env : TypeEnv s} (h : env.is_downward_closed)
    (cs : CaptureSet {}) : (env.extend_cvar cs).is_downward_closed := by
  intro X
  obtain ⟨X0, hX0⟩ := TypeEnv.extend_cvar_lookup_tvar env cs X
  rw [hX0]; exact h X0

theorem TypeEnv.is_transparent.extend_cvar {env : TypeEnv s} (h : env.is_transparent)
    (cs : CaptureSet {}) : (env.extend_cvar cs).is_transparent := by
  intro X
  obtain ⟨X0, hX0⟩ := TypeEnv.extend_cvar_lookup_tvar env cs X
  rw [hX0]; exact h X0

theorem TypeEnv.is_bool_independent.extend_cvar {env : TypeEnv s}
    (h : env.is_bool_independent) (cs : CaptureSet {}) :
    (env.extend_cvar cs).is_bool_independent := by
  intro X
  obtain ⟨X0, hX0⟩ := TypeEnv.extend_cvar_lookup_tvar env cs X
  rw [hX0]; exact h X0

/-! ## Monotonicity of capture-set denotations -/

theorem ground_denot_is_monotonic {C : CaptureSet {}} :
  (C.ground_denot).is_monotonic_for C := by
  unfold CapDenot.is_monotonic_for
  intro m1 m2 hwf hsub
  induction C with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    unfold CaptureSet.ground_denot
    cases hwf with
    | wf_union hwf1 hwf2 =>
      have e1 := ih1 hwf1
      have e2 := ih2 hwf2
      simp only [e1, e2]
  | var v =>
    cases v with
    | bound x => cases x
    | free x =>
      unfold CaptureSet.ground_denot
      cases hwf with
      | wf_var_free hex =>
        exact (reachability_of_loc_monotonic hsub x hex).symm
  | cvar c => cases c

theorem capture_set_denot_is_monotonic {C : CaptureSet s} :
  (C.denot ρ).is_monotonic_for (C.subst (Subst.from_TypeEnv ρ)) := by
  unfold CapDenot.is_monotonic_for
  intro m1 m2 hwf hsub
  induction C with
  | empty => rfl
  | union C1 C2 ih1 ih2 =>
    unfold CaptureSet.denot
    simp only [CaptureSet.subst, CaptureSet.ground_denot] at hwf ⊢
    cases hwf with
    | wf_union hwf1 hwf2 =>
      have e1 := ih1 hwf1
      have e2 := ih2 hwf2
      unfold CaptureSet.denot at e1 e2
      rw [e1, e2]
  | var v =>
    cases v with
    | bound x =>
      unfold CaptureSet.denot
      simp only [CaptureSet.subst, Subst.from_TypeEnv, Var.subst, TypeEnv.lookup_var] at hwf
      simp only [CaptureSet.subst, Subst.from_TypeEnv, Var.subst, TypeEnv.lookup_var]
      unfold CaptureSet.ground_denot
      cases hwf with
      | wf_var_free hex =>
        exact (reachability_of_loc_monotonic hsub (ρ.lookup_var x) hex).symm
    | free x =>
      unfold CaptureSet.denot
      simp only [CaptureSet.subst, Var.subst] at hwf
      simp only [CaptureSet.subst, Var.subst]
      unfold CaptureSet.ground_denot
      cases hwf with
      | wf_var_free hex =>
        exact (reachability_of_loc_monotonic hsub x hex).symm
  | cvar c =>
    unfold CaptureSet.denot
    simp only [CaptureSet.subst, Subst.from_TypeEnv, TypeEnv.lookup_cvar]
    exact ground_denot_is_monotonic hwf hsub

theorem capture_bound_denot_is_monotonic {B : CaptureBound s}
  (hwf : (B.subst (Subst.from_TypeEnv ρ)).WfInHeap m1.heap)
  (hsub : m2.subsumes m1) :
  B.denot ρ m1 = B.denot ρ m2 := by
  cases B with
  | unbound =>
    unfold CaptureBound.denot
    rfl
  | bound cs =>
    unfold CaptureBound.denot
    simp only [CaptureBound.subst] at hwf
    cases hwf with
    | wf_bound hwf_cs =>
      simp only []
      rw [capture_set_denot_is_monotonic hwf_cs hsub]


/-! ## Transparency and bool-independence -/

theorem shape_val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_transparent := by
  intro C k st
  cases T with
  | top =>
    intro m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    constructor
    · exact .wf_var (.wf_free hx)
    · simp only [resolve_reachability]
      have hx_heap : m.heap x = some (Cell.val v) := hx
      rw [reachability_of_loc_eq_resolve_reachability m x v hx_heap]
      exact ht.2
  | tvar X =>
    simp only [Ty.shape_val_denot]
    exact henv X C k st
  | unit =>
    intro m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := hx
    rw [resolve_var_heap_trans hx']
    exact ht
  | cap =>
    intro m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨_, label, hlabel, hcap, hmem⟩ := ht
    have hval := v.isVal
    rw [hlabel] at hval
    cases hval
  | arrow T1 T2 =>
    intro m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    have ⟨hwf_unwrap, hexists⟩ := ht
    exact ⟨.wf_var (.wf_free hx'), hexists⟩
  | bool =>
    intro m x v hx ht
    cases v with
    | mk vexp hv_simple hreach =>
      have hlookup : m.heap x = some (Cell.val ⟨vexp, hv_simple, hreach⟩) := hx
      have hres_self : resolve m.heap vexp = some vexp := by
        cases hv_simple <;> simp [resolve]
      have hbool : vexp = .btrue ∨ vexp = .bfalse := by
        simpa [Ty.shape_val_denot, hres_self] using ht
      cases hbool with
      | inl hb => simp [Ty.shape_val_denot, resolve, hlookup, hb]
      | inr hb => simp [Ty.shape_val_denot, resolve, hlookup, hb]
  | cell T =>
    intro m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨l, n0, Rl, heq, _⟩ := ht
    have hval := v.isVal
    rw [heq] at hval
    cases hval
  | poly T1 T2 =>
    intro m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    have ⟨hwf_unwrap, hexists⟩ := ht
    exact ⟨.wf_var (.wf_free hx'), hexists⟩
  | cpoly B T =>
    intro m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    have ⟨hwf_unwrap, hexists⟩ := ht
    exact ⟨.wf_var (.wf_free hx'), hexists⟩

theorem shape_val_denot_is_bool_independent {env : TypeEnv s}
  (henv : env.is_bool_independent)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_bool_independent := by
  intro C k st m
  cases T with
  | top =>
    simp only [Ty.shape_val_denot, resolve_reachability]
    constructor <;> intro h
    · exact ⟨Exp.WfInHeap.wf_bfalse, h.2⟩
    · exact ⟨Exp.WfInHeap.wf_btrue, h.2⟩
  | tvar X =>
    simp only [Ty.shape_val_denot]
    exact henv X C k st
  | unit => simp [Ty.shape_val_denot, resolve]
  | cap => simp [Ty.shape_val_denot]
  | bool => simp [Ty.shape_val_denot, resolve]
  | cell T => simp [Ty.shape_val_denot]
  | arrow T1 T2 => simp [Ty.shape_val_denot, resolve]
  | poly T1 T2 => simp [Ty.shape_val_denot, resolve]
  | cpoly B T => simp [Ty.shape_val_denot, resolve]

theorem capt_val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .capt s) :
  (Ty.capt_val_denot env T).is_transparent := by
  cases T with
  | capt C S =>
    intro k st m x v hx ht
    simp only [Ty.capt_val_denot] at ht ⊢
    have ⟨hsv, hwf, hwf_C, hshape⟩ := ht
    exact ⟨.is_var, .wf_var (.wf_free hx), hwf_C,
      shape_val_denot_is_transparent henv S (C.denot env m) k st hx hshape⟩

theorem exi_val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env T).is_transparent := by
  cases T with
  | typ T =>
    simp only [Ty.exi_val_denot]
    exact capt_val_denot_is_transparent henv T
  | exi T =>
    intro k st m x v hx ht
    simp only [Ty.exi_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := hx
    rw [resolve_var_heap_trans hx']
    exact ht

theorem capt_val_denot_is_bool_independent {env : TypeEnv s}
  (henv : TypeEnv.is_bool_independent env)
  (T : Ty .capt s) :
  (Ty.capt_val_denot env T).is_bool_independent := by
  cases T with
  | capt C S =>
    intro k st m
    simp only [Ty.capt_val_denot]
    constructor
    · intro ⟨hsimple, hwf, hwf_C, hshape⟩
      exact ⟨.is_simple_val .bfalse, .wf_bfalse, hwf_C,
             (shape_val_denot_is_bool_independent henv S (C.denot env m) k st).mp hshape⟩
    · intro ⟨hsimple, hwf, hwf_C, hshape⟩
      exact ⟨.is_simple_val .btrue, .wf_btrue, hwf_C,
             (shape_val_denot_is_bool_independent henv S (C.denot env m) k st).mpr hshape⟩

theorem exi_val_denot_is_bool_independent {env : TypeEnv s}
  (henv : TypeEnv.is_bool_independent env)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env T).is_bool_independent := by
  cases T with
  | typ T =>
    simp only [Ty.exi_val_denot]
    exact capt_val_denot_is_bool_independent henv T
  | exi T =>
    intro k st m
    simp only [Ty.exi_val_denot]
    constructor
    · rintro ⟨CS, x, hres, -⟩; cases hres
    · rintro ⟨CS, x, hres, -⟩; cases hres

/-! ## Monotonicity along the typed future relation -/

theorem shape_val_denot_worldle_mono {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).worldle_monotonic := by
  intro C k st1 st2 m1 m2 e hwle ht
  have hmem : m2.subsumes m1 := hwle.1
  cases T with
  | top =>
    simp only [Ty.shape_val_denot] at ht ⊢
    constructor
    · exact Exp.wf_monotonic hmem ht.1
    · have heq := resolve_reachability_monotonic hmem e ht.1
      rw [heq]
      exact ht.2
  | tvar X =>
    simp only [Ty.shape_val_denot] at ht ⊢
    exact henv.tvar_worldle X C hwle ht
  | unit =>
    simp only [Ty.shape_val_denot] at ht ⊢
    exact resolve_monotonic hmem ht
  | cap =>
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf_e, label, heq, hcap, hmemin⟩ := ht
    refine ⟨Exp.wf_monotonic hmem hwf_e, label, heq, ?_, hmemin⟩
    have hsub : m2.heap.subsumes m1.heap := hmem
    obtain ⟨c', hc', hsub_c⟩ := hsub label (Cell.capability .basic) hcap
    simp only [Cell.subsumes] at hsub_c
    subst hsub_c
    exact hc'
  | bool =>
    simp only [Ty.shape_val_denot] at ht ⊢
    cases ht with
    | inl htrue => exact Or.inl (resolve_monotonic hmem htrue)
    | inr hfalse => exact Or.inr (resolve_monotonic hmem hfalse)
  | cell T =>
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨l, n0, Rl, heq, hlookup, hmem_l, hst, hbi⟩ := ht
    have hsub : m2.heap.subsumes m1.heap := hmem
    obtain ⟨c', hc', hsub_c⟩ := hsub l (Cell.capability (.mcell n0)) hlookup
    cases c' with
    | val v => cases hsub_c
    | masked => cases hsub_c
    | capability info =>
      cases info with
      | basic => cases hsub_c
      | mcell n' =>
        exact ⟨l, n', Rl, heq, hc', hmem_l, hwle.2 l Rl hst, hbi⟩
  | arrow T1 T2 =>
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf_e, cs, T0, t0, hr, hwf_cs, hR0_sub, hfun⟩ := ht
    have heq := expand_captures_monotonic hmem cs hwf_cs
    refine ⟨Exp.wf_monotonic hmem hwf_e, cs, T0, t0, resolve_monotonic hmem hr,
      CaptureSet.wf_monotonic hmem hwf_cs, by rw [heq]; exact hR0_sub, ?_⟩
    intro j hjk st' m' arg hwle' harg
    rw [heq]
    exact hfun j hjk st' m' arg (WorldLe.trans (WorldLe.trunc hjk hwle) hwle') harg
  | poly T1 T2 =>
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf_e, cs, S0, t0, hr, hwf_cs, hR0_sub, hfun⟩ := ht
    have heq := expand_captures_monotonic hmem cs hwf_cs
    refine ⟨Exp.wf_monotonic hmem hwf_e, cs, S0, t0, resolve_monotonic hmem hr,
      CaptureSet.wf_monotonic hmem hwf_cs, by rw [heq]; exact hR0_sub, ?_⟩
    intro j hjk st' m' denot hwle' hproper himply
    rw [heq]
    exact hfun j hjk st' m' denot (WorldLe.trans (WorldLe.trunc hjk hwle) hwle') hproper himply
  | cpoly B T =>
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf_e, cs, B0, t0, hr, hwf_cs, hR0_sub, hfun⟩ := ht
    have heq := expand_captures_monotonic hmem cs hwf_cs
    refine ⟨Exp.wf_monotonic hmem hwf_e, cs, B0, t0, resolve_monotonic hmem hr,
      CaptureSet.wf_monotonic hmem hwf_cs, by rw [heq]; exact hR0_sub, ?_⟩
    intro j hjk st' m' CS hwf hwle' hbound
    rw [heq]
    exact hfun j hjk st' m' CS hwf (WorldLe.trans (WorldLe.trunc hjk hwle) hwle') hbound

theorem capt_val_denot_worldle_mono {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .capt s) :
  (Ty.capt_val_denot env T).worldle_monotonic := by
  cases T with
  | capt C S =>
    intro k st1 st2 m1 m2 e hwle ht
    have hmem : m2.subsumes m1 := hwle.1
    simp only [Ty.capt_val_denot] at ht ⊢
    have ⟨hsv, hwf, hwf_C, hshape⟩ := ht
    refine ⟨hsv, Exp.wf_monotonic hmem hwf, CaptureSet.wf_monotonic hmem hwf_C, ?_⟩
    have h := capture_set_denot_is_monotonic hwf_C hmem
    rw [<-h]
    exact shape_val_denot_worldle_mono henv S (C.denot env m1) hwle hshape

theorem exi_val_denot_worldle_mono {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env T).worldle_monotonic := by
  cases T with
  | typ T =>
    simp only [Ty.exi_val_denot]
    exact capt_val_denot_worldle_mono henv T
  | exi T =>
    intro k st1 st2 m1 m2 e hwle ht
    have hmem : m2.subsumes m1 := hwle.1
    simp only [Ty.exi_val_denot] at ht ⊢
    obtain ⟨CS, y, hres, hwf_CS, hbody⟩ := ht
    exact ⟨CS, y, resolve_monotonic hmem hres, CaptureSet.wf_monotonic hmem hwf_CS,
      capt_val_denot_worldle_mono (henv.extend_cvar CS) T hwle hbody⟩

theorem shape_val_denot_is_monotonic {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_monotonic :=
  fun C _ _ _ _ _ hmem ht =>
    shape_val_denot_worldle_mono henv T C (WorldLe.of_subsumes hmem) ht

theorem capt_val_denot_is_monotonic {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .capt s) :
  (Ty.capt_val_denot env T).is_monotonic :=
  fun _ _ _ _ _ hmem ht =>
    capt_val_denot_worldle_mono henv T (WorldLe.of_subsumes hmem) ht

theorem exi_val_denot_is_monotonic {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env T).is_monotonic :=
  fun _ _ _ _ _ hmem ht =>
    exi_val_denot_worldle_mono henv T (WorldLe.of_subsumes hmem) ht

/-! ## Downward closure in the step index -/

theorem shape_val_denot_down_trunc {env : TypeEnv s}
  (hdc : env.is_downward_closed)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_downward_closed := by
  intro C j k hjk st m e ht
  cases T with
  | top => simp only [Ty.shape_val_denot] at ht ⊢; exact ht
  | tvar X =>
    simp only [Ty.shape_val_denot] at ht ⊢
    exact hdc X C hjk ht
  | unit => simp only [Ty.shape_val_denot] at ht ⊢; exact ht
  | cap => simp only [Ty.shape_val_denot] at ht ⊢; exact ht
  | bool => simp only [Ty.shape_val_denot] at ht ⊢; exact ht
  | cell T =>
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨l, n0, Rl, heq, hlookup, hmem_l, hst, hbi⟩ := ht
    refine ⟨l, n0, _, heq, hlookup, hmem_l, by rw [World.trunc_lookup, hst]; rfl, ?_⟩
    intro i w' m' e'
    exact hbi ⟨i.val, Nat.lt_of_lt_of_le i.isLt hjk⟩ w' m' e'
  | arrow T1 T2 =>
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf_e, cs, T0, t0, hr, hwf_cs, hR0_sub, hfun⟩ := ht
    refine ⟨hwf_e, cs, T0, t0, hr, hwf_cs, hR0_sub, ?_⟩
    intro i hij st' m' arg hwle' harg
    rw [World.trunc_trunc] at hwle'
    exact hfun i (Nat.le_trans hij hjk) st' m' arg hwle' harg
  | poly T1 T2 =>
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf_e, cs, S0, t0, hr, hwf_cs, hR0_sub, hfun⟩ := ht
    refine ⟨hwf_e, cs, S0, t0, hr, hwf_cs, hR0_sub, ?_⟩
    intro i hij st' m' denot hwle' hproper himply
    rw [World.trunc_trunc] at hwle'
    exact hfun i (Nat.le_trans hij hjk) st' m' denot hwle' hproper himply
  | cpoly B T =>
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf_e, cs, B0, t0, hr, hwf_cs, hR0_sub, hfun⟩ := ht
    refine ⟨hwf_e, cs, B0, t0, hr, hwf_cs, hR0_sub, ?_⟩
    intro i hij st' m' CS hwf hwle' hbound
    rw [World.trunc_trunc] at hwle'
    exact hfun i (Nat.le_trans hij hjk) st' m' CS hwf hwle' hbound

theorem capt_val_denot_down_trunc {env : TypeEnv s}
  (hdc : env.is_downward_closed)
  (T : Ty .capt s) :
  (Ty.capt_val_denot env T).is_downward_closed := by
  cases T with
  | capt C S =>
    intro j k hjk st m e ht
    simp only [Ty.capt_val_denot] at ht ⊢
    have ⟨hsv, hwf, hwf_C, hshape⟩ := ht
    exact ⟨hsv, hwf, hwf_C, shape_val_denot_down_trunc hdc S (C.denot env m) hjk hshape⟩

theorem exi_val_denot_down_trunc {env : TypeEnv s}
  (hdc : env.is_downward_closed)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env T).is_downward_closed := by
  cases T with
  | typ T =>
    simp only [Ty.exi_val_denot]
    exact capt_val_denot_down_trunc hdc T
  | exi T =>
    intro j k hjk st m e ht
    simp only [Ty.exi_val_denot] at ht ⊢
    obtain ⟨CS, y, hres, hwf_CS, hbody⟩ := ht
    exact ⟨CS, y, hres, hwf_CS, capt_val_denot_down_trunc (hdc.extend_cvar CS) T hjk hbody⟩

/-! ## Environment typing along worlds -/

/-- Environment typing descends along the typed future relation and an index drop. -/
theorem env_typing_worldle_trunc {Γ : Ctx s} {env : TypeEnv s}
    {j k : Nat} (hjk : j ≤ k) {st : StoreTyping k} {st' : StoreTyping j} {m m' : Memory}
    (hts : EnvTyping Γ env k st m) (hwle : WorldLe st' m' (st.trunc hjk) m) :
    EnvTyping Γ env j st' m' := by
  induction Γ with
  | empty =>
    cases env with
    | empty => trivial
  | push Γ item ih =>
    cases env with
    | extend env' info =>
      cases item with
      | var T =>
        cases info with
        | var n =>
          unfold EnvTyping at hts ⊢
          obtain ⟨hval, ht'⟩ := hts
          refine ⟨?_, ih ht'⟩
          have hdown := capt_val_denot_down_trunc (typed_env_is_downward_closed ht') T hjk hval
          exact capt_val_denot_worldle_mono (typed_env_is_monotonic ht') T hwle hdown
      | tvar S =>
        cases info with
        | tvar d =>
          simp only [EnvTyping] at hts ⊢
          obtain ⟨hproper, himply, ht'⟩ := hts
          exact ⟨hproper,
            IPreDenot.imply_after_worldle (IPreDenot.ImplyAfter.trunc hjk himply) hwle, ih ht'⟩
      | cvar B =>
        cases info with
        | cvar cs =>
          simp only [EnvTyping] at hts ⊢
          obtain ⟨hwf, hwf_bound, hsub, ht'⟩ := hts
          have hmem : m'.subsumes m := hwle.1
          have h_denot_eq := ground_denot_is_monotonic hwf hmem
          have h_bound_eq : B.denot env' m = B.denot env' m' :=
            capture_bound_denot_is_monotonic hwf_bound hmem
          refine ⟨CaptureSet.wf_monotonic hmem hwf, CaptureBound.wf_monotonic hmem hwf_bound,
            ?_, ih ht'⟩
          rw [← h_denot_eq, ← h_bound_eq]
          exact hsub

/-- Environment typing is monotone along the typed future relation at a fixed index. -/
theorem env_typing_worldle_down {Γ : Ctx s} {env : TypeEnv s}
    {k : Nat} {st st' : StoreTyping k} {m m' : Memory}
    (hts : EnvTyping Γ env k st m) (hwle : WorldLe st' m' st m) :
    EnvTyping Γ env k st' m' :=
  env_typing_worldle_trunc (Nat.le_refl k) hts (by rw [World.trunc_self]; exact hwle)

/-- Environment typing is monotone under memory subsumption. -/
theorem env_typing_monotonic {Γ : Ctx s} {env : TypeEnv s} {k : Nat} {st : StoreTyping k}
    {mem1 mem2 : Memory}
    (ht : EnvTyping Γ env k st mem1)
    (hmem : mem2.subsumes mem1) :
    EnvTyping Γ env k st mem2 :=
  env_typing_worldle_down ht (WorldLe.of_subsumes hmem)

/-! ## Semantic subcapturing and subtyping -/

/-- Semantic subcapturing. -/
def SemSubcapt (Γ : Ctx s) (C1 C2 : CaptureSet s) : Prop :=
  ∀ env k st m,
    EnvTyping Γ env k st m ->
    C1.denot env m ⊆ C2.denot env m

def SemSubtyp {sort : TySort} (Γ : Ctx s) (T1 T2 : Ty sort s) : Prop :=
  match sort with
  | .shape =>
    ∀ env k st m, EnvTyping Γ env k st m ->
      (Ty.shape_val_denot env T1).ImplyAfter k st m (Ty.shape_val_denot env T2)
  | .capt =>
    ∀ env k st m, EnvTyping Γ env k st m ->
      (Ty.capt_val_denot env T1).ImplyAfter k st m (Ty.capt_val_denot env T2)
  | .exi =>
    ∀ env k st m, EnvTyping Γ env k st m ->
      (Ty.exi_val_denot env T1).ImplyAfter k st m (Ty.exi_val_denot env T2)


/-! ## Reachability properties of shape denotations -/

theorem shape_val_denot_is_reachability_safe {env : TypeEnv s}
  (hts : env.is_reachability_safe)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_reachability_safe := by
  intro R k st m e hdenot
  cases T with
  | top =>
    simp only [Ty.shape_val_denot] at hdenot
    exact hdenot.2
  | tvar X =>
    simp only [Ty.shape_val_denot] at hdenot
    exact hts X R k st m e hdenot
  | bool =>
    simp only [Ty.shape_val_denot] at hdenot
    cases e with
    | btrue =>
      simp only [resolve_reachability]
      exact CapabilitySet.Subset.empty
    | bfalse =>
      simp only [resolve_reachability]
      exact CapabilitySet.Subset.empty
    | var x =>
      cases x with
      | bound bx => cases bx
      | free fx =>
        cases hcell : m.heap fx with
        | none =>
          simp [resolve, hcell] at hdenot
        | some cell =>
          cases cell with
          | capability =>
            simp [resolve, hcell] at hdenot
          | masked =>
            simp [resolve, hcell] at hdenot
          | val hv =>
            cases hv with
            | mk vexp hv_simple hreach_val =>
              have hreach :=
                Memory.reachability_invariant m fx ⟨vexp, hv_simple, hreach_val⟩
                  (by simp [hcell])
              cases hv_simple with
              | abs =>
                simp [resolve, hcell] at hdenot ⊢
              | tabs =>
                simp [resolve, hcell] at hdenot ⊢
              | cabs =>
                simp [resolve, hcell] at hdenot ⊢
              | unit =>
                simp [resolve, hcell] at hdenot ⊢
              | btrue =>
                have hreach_empty : hreach_val = {} := by
                  simpa [compute_reachability] using hreach
                simp only [resolve_reachability, reachability_of_loc, hcell, hreach_empty]
                exact CapabilitySet.Subset.empty
              | bfalse =>
                have hreach_empty : hreach_val = {} := by
                  simpa [compute_reachability] using hreach
                simp only [resolve_reachability, reachability_of_loc, hcell, hreach_empty]
                exact CapabilitySet.Subset.empty
    | _ =>
      simp [resolve] at hdenot
  | cell T =>
    simp only [Ty.shape_val_denot] at hdenot
    obtain ⟨l, n0, Rl, heq, hlookup, hmem, _, _⟩ := hdenot
    rw [heq]
    simp only [resolve_reachability]
    have hlookup' : m.heap l = some (Cell.capability (.mcell n0)) := hlookup
    simp only [reachability_of_loc, hlookup']
    exact CapabilitySet.mem_imp_singleton_subset hmem
  | unit =>
    have hdenot' : resolve m.heap e = some .unit := by
      simpa only [Ty.shape_val_denot] using hdenot
    cases e with
    | unit =>
      change ({} : CapabilitySet) ⊆ R
      exact CapabilitySet.Subset.empty
    | var x =>
      cases x with
      | free fx =>
        change reachability_of_loc m.heap fx ⊆ R
        cases hfx : m.heap fx with
        | none =>
          have hbad : (none : Option (Exp {})) = some .unit := by
            simpa only [resolve, hfx] using hdenot'
          cases hbad
        | some cell =>
          cases cell with
          | capability =>
            have hbad : (none : Option (Exp {})) = some .unit := by
              simpa only [resolve, hfx] using hdenot'
            cases hbad
          | masked =>
            have hbad : (none : Option (Exp {})) = some .unit := by
              simpa only [resolve, hfx] using hdenot'
            cases hbad
          | val v =>
            cases v with
            | mk vexp hv_simple hreach_val =>
              have hresolve : some vexp = some .unit := by
                simpa only [resolve, hfx] using hdenot'
              have hreach :=
                Memory.reachability_invariant m fx ⟨vexp, hv_simple, hreach_val⟩
                  (by simp [hfx])
              cases hv_simple with
              | abs => cases hresolve
              | tabs => cases hresolve
              | cabs => cases hresolve
              | unit =>
                have hreach_empty : hreach_val = {} := by
                  simpa [compute_reachability] using hreach
                rw [reachability_of_loc, hfx, hreach_empty]
                exact CapabilitySet.Subset.empty
              | btrue => cases hresolve
              | bfalse => cases hresolve
      | bound bx => cases bx
    | _ =>
      cases hdenot'
  | cap =>
    simp only [Ty.shape_val_denot] at hdenot
    have ⟨hwf_e, label, heq, hcap, hmem⟩ := hdenot
    rw [heq]
    simp only [resolve_reachability]
    have hcap' : m.heap label = some (Cell.capability .basic) := hcap
    simp only [reachability_of_loc, hcap']
    exact CapabilitySet.mem_imp_singleton_subset hmem
  | arrow T1 T2 =>
    simp only [Ty.shape_val_denot] at hdenot
    have ⟨hwf_e, cs, T0, t0, hres, hwf_cs, hR0_sub, _⟩ := hdenot
    cases e with
    | abs cs' T0' t0' =>
      change expand_captures m.heap cs' ⊆ R
      have hres' : some (Exp.abs cs' T0' t0') = some (Exp.abs cs T0 t0) := by
        simpa only [resolve] using hres
      cases hres'
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        change reachability_of_loc m.heap fx ⊆ R
        cases hfx : m.heap fx with
        | none =>
          have hbad : (none : Option (Exp {})) = some (Exp.abs cs T0 t0) := by
            simpa only [resolve, hfx] using hres
          cases hbad
        | some cell =>
          cases cell with
          | capability =>
            have hbad : (none : Option (Exp {})) = some (Exp.abs cs T0 t0) := by
              simpa only [resolve, hfx] using hres
            cases hbad
          | masked =>
            have hbad : (none : Option (Exp {})) = some (Exp.abs cs T0 t0) := by
              simpa only [resolve, hfx] using hres
            cases hbad
          | val v =>
            have hres' : some v.unwrap = some (Exp.abs cs T0 t0) := by
              simpa only [resolve, hfx] using hres
            have hv_heap : m.heap fx = some (Cell.val v) := hfx
            rw [reachability_of_loc_eq_resolve_reachability m fx v hv_heap]
            injection hres' with hunwrap
            rw [hunwrap]
            change expand_captures m.heap cs ⊆ R
            exact hR0_sub
      | bound bx => cases bx
    | _ => cases hres
  | poly T1 T2 =>
    simp only [Ty.shape_val_denot] at hdenot
    have ⟨hwf_e, cs, S0, t0, hres, hwf_cs, hR0_sub, _⟩ := hdenot
    cases e with
    | tabs cs' S0' t0' =>
      change expand_captures m.heap cs' ⊆ R
      have hres' : some (Exp.tabs cs' S0' t0') = some (Exp.tabs cs S0 t0) := by
        simpa only [resolve] using hres
      cases hres'
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        change reachability_of_loc m.heap fx ⊆ R
        cases hfx : m.heap fx with
        | none =>
          have hbad : (none : Option (Exp {})) = some (Exp.tabs cs S0 t0) := by
            simpa only [resolve, hfx] using hres
          cases hbad
        | some cell =>
          cases cell with
          | capability =>
            have hbad : (none : Option (Exp {})) = some (Exp.tabs cs S0 t0) := by
              simpa only [resolve, hfx] using hres
            cases hbad
          | masked =>
            have hbad : (none : Option (Exp {})) = some (Exp.tabs cs S0 t0) := by
              simpa only [resolve, hfx] using hres
            cases hbad
          | val v =>
            have hres' : some v.unwrap = some (Exp.tabs cs S0 t0) := by
              simpa only [resolve, hfx] using hres
            have hv_heap : m.heap fx = some (Cell.val v) := hfx
            rw [reachability_of_loc_eq_resolve_reachability m fx v hv_heap]
            injection hres' with hunwrap
            rw [hunwrap]
            change expand_captures m.heap cs ⊆ R
            exact hR0_sub
      | bound bx => cases bx
    | _ => cases hres
  | cpoly B T =>
    simp only [Ty.shape_val_denot] at hdenot
    have ⟨hwf_e, cs, B0, t0, hres, hwf_cs, hR0_sub, _⟩ := hdenot
    cases e with
    | cabs cs' B0' t0' =>
      change expand_captures m.heap cs' ⊆ R
      have hres' : some (Exp.cabs cs' B0' t0') = some (Exp.cabs cs B0 t0) := by
        simpa only [resolve] using hres
      cases hres'
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        change reachability_of_loc m.heap fx ⊆ R
        cases hfx : m.heap fx with
        | none =>
          have hbad : (none : Option (Exp {})) = some (Exp.cabs cs B0 t0) := by
            simpa only [resolve, hfx] using hres
          cases hbad
        | some cell =>
          cases cell with
          | capability =>
            have hbad : (none : Option (Exp {})) = some (Exp.cabs cs B0 t0) := by
              simpa only [resolve, hfx] using hres
            cases hbad
          | masked =>
            have hbad : (none : Option (Exp {})) = some (Exp.cabs cs B0 t0) := by
              simpa only [resolve, hfx] using hres
            cases hbad
          | val v =>
            have hres' : some v.unwrap = some (Exp.cabs cs B0 t0) := by
              simpa only [resolve, hfx] using hres
            have hv_heap : m.heap fx = some (Cell.val v) := hfx
            rw [reachability_of_loc_eq_resolve_reachability m fx v hv_heap]
            injection hres' with hunwrap
            rw [hunwrap]
            change expand_captures m.heap cs ⊆ R
            exact hR0_sub
      | bound bx => cases bx
    | _ => cases hres

theorem shape_val_denot_is_reachability_monotonic {env : TypeEnv s}
  (hts : env.is_reachability_monotonic)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_reachability_monotonic := by
  intro R1 R2 hsub k st m e hdenot
  cases T with
  | top =>
    simp only [Ty.shape_val_denot] at hdenot ⊢
    exact ⟨hdenot.1, CapabilitySet.Subset.trans hdenot.2 hsub⟩
  | tvar X =>
    simp only [Ty.shape_val_denot] at hdenot ⊢
    exact hts X R1 R2 hsub k st m e hdenot
  | bool =>
    simp only [Ty.shape_val_denot] at hdenot ⊢
    exact hdenot
  | cell T =>
    simp only [Ty.shape_val_denot] at hdenot ⊢
    obtain ⟨l, n0, Rl, heq, hlookup, hmem, hst, hbi⟩ := hdenot
    exact ⟨l, n0, Rl, heq, hlookup, CapabilitySet.subset_preserves_mem hsub hmem, hst, hbi⟩
  | unit =>
    simp only [Ty.shape_val_denot] at hdenot ⊢
    exact hdenot
  | cap =>
    simp only [Ty.shape_val_denot] at hdenot ⊢
    have ⟨hwf_e, label, heq, hcap, hmem⟩ := hdenot
    exact ⟨hwf_e, label, heq, hcap, CapabilitySet.subset_preserves_mem hsub hmem⟩
  | arrow T1 T2 =>
    simp only [Ty.shape_val_denot] at hdenot ⊢
    have ⟨hwf_e, cs, T0, t0, hres, hwf_cs, hR0_R1, hfun⟩ := hdenot
    exact ⟨hwf_e, cs, T0, t0, hres, hwf_cs, CapabilitySet.Subset.trans hR0_R1 hsub, hfun⟩
  | poly T1 T2 =>
    simp only [Ty.shape_val_denot] at hdenot ⊢
    have ⟨hwf_e, cs, T0, t0, hres, hwf_cs, hR0_R1, hfun⟩ := hdenot
    exact ⟨hwf_e, cs, T0, t0, hres, hwf_cs, CapabilitySet.Subset.trans hR0_R1 hsub, hfun⟩
  | cpoly B T =>
    simp only [Ty.shape_val_denot] at hdenot ⊢
    have ⟨hwf_e, cs, B0, t0, hres, hwf_cs, hR0_R1, hfun⟩ := hdenot
    exact ⟨hwf_e, cs, B0, t0, hres, hwf_cs, CapabilitySet.Subset.trans hR0_R1 hsub, hfun⟩

lemma wf_from_resolve_unit
  {m : Memory} {e : Exp {}}
  (hresolve : resolve m.heap e = some .unit) :
  e.WfInHeap m.heap := by
  cases e with
  | var x =>
    cases x with
    | free fx =>
      simp only [resolve] at hresolve
      cases hfx : m.heap fx with
      | none =>
        rw [hfx] at hresolve
        cases hresolve
      | some cell =>
        exact .wf_var (.wf_free hfx)
    | bound bx => cases bx
  | unit => exact .wf_unit
  | _ => simp [resolve] at hresolve

theorem shape_val_denot_implies_wf {env : TypeEnv s}
  (hts : env.is_implying_wf)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).implies_wf := by
  intro R k st m e hdenot
  cases T with
  | top =>
    simp only [Ty.shape_val_denot] at hdenot
    exact hdenot.1
  | tvar X =>
    simp only [Ty.shape_val_denot] at hdenot
    exact hts X R k st m e hdenot
  | bool =>
    simp only [Ty.shape_val_denot] at hdenot
    cases e with
    | btrue => exact Exp.WfInHeap.wf_btrue
    | bfalse => exact Exp.WfInHeap.wf_bfalse
    | var x =>
      cases x with
      | bound bx => cases bx
      | free fx =>
        cases hcell : m.heap fx with
        | none =>
          simp [resolve, hcell] at hdenot
        | some cell =>
          cases cell with
          | val hv =>
            exact .wf_var (.wf_free (by simpa [Memory.lookup] using hcell))
          | capability =>
            simp [resolve, hcell] at hdenot
          | masked =>
            simp [resolve, hcell] at hdenot
    | _ =>
      simp [resolve] at hdenot
  | unit =>
    simp only [Ty.shape_val_denot] at hdenot
    exact wf_from_resolve_unit hdenot
  | cell T =>
    simp only [Ty.shape_val_denot] at hdenot
    obtain ⟨l, n0, Rl, heq, hlookup, _⟩ := hdenot
    rw [heq]
    exact .wf_var (.wf_free (by simp only [Memory.lookup] at hlookup; exact hlookup))
  | cap =>
    simp only [Ty.shape_val_denot] at hdenot
    exact hdenot.1
  | arrow T1 T2 =>
    simp only [Ty.shape_val_denot] at hdenot
    exact hdenot.1
  | poly T1 T2 =>
    simp only [Ty.shape_val_denot] at hdenot
    exact hdenot.1
  | cpoly B T =>
    simp only [Ty.shape_val_denot] at hdenot
    exact hdenot.1

theorem shape_val_denot_is_tight {env : TypeEnv s}
  (hts : env.is_tight) (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_tight := by
  intro R k st m fx ht
  cases T with
  | top =>
    simp only [Ty.shape_val_denot, resolve_reachability] at ht ⊢
    exact ⟨ht.1, CapabilitySet.Subset.refl⟩
  | tvar X =>
    simp only [Ty.shape_val_denot] at ht ⊢
    exact hts X R k st m fx ht
  | bool =>
    simp only [Ty.shape_val_denot] at ht ⊢
    exact ht
  | unit =>
    simp only [Ty.shape_val_denot] at ht ⊢
    exact ht
  | cell T =>
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨l, n0, Rl, heq, hlookup, hmem, hst, hbi⟩ := ht
    have hfx_eq_l : fx = l := by
      injection heq with _ h
      injection h with h
    subst hfx_eq_l
    refine ⟨fx, n0, Rl, rfl, hlookup, ?_, hst, hbi⟩
    simp only [Memory.lookup] at hlookup
    simp only [reachability_of_loc, hlookup]
    exact CapabilitySet.mem.here
  | cap =>
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨hwf, label, heq, hlookup, _⟩ := ht
    cases heq
    refine ⟨hwf, fx, rfl, hlookup, ?_⟩
    simp only [Memory.lookup] at hlookup
    simp only [reachability_of_loc, hlookup]
    exact CapabilitySet.mem.here
  | arrow T1 T2 =>
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf, cs, T0, t0, hresolve, hwf_cs, hR0_sub, hbody⟩ := ht
    refine ⟨hwf, cs, T0, t0, hresolve, hwf_cs, ?_, hbody⟩
    have hstored : ∃ v, m.heap fx = some (Cell.val v) ∧
        v.unwrap = Exp.abs cs T0 t0 := by
      cases heq : m.heap fx with
      | none =>
        have hbad : (none : Option (Exp {})) = some (Exp.abs cs T0 t0) := by
          simpa only [resolve, heq] using hresolve
        cases hbad
      | some cell =>
        cases cell with
        | capability =>
          have hbad : (none : Option (Exp {})) = some (Exp.abs cs T0 t0) := by
            simpa only [resolve, heq] using hresolve
          cases hbad
        | masked =>
          have hbad : (none : Option (Exp {})) = some (Exp.abs cs T0 t0) := by
            simpa only [resolve, heq] using hresolve
          cases hbad
        | val v =>
          have hunwrap : some v.unwrap = some (Exp.abs cs T0 t0) := by
            simpa only [resolve, heq] using hresolve
          injection hunwrap with hunwrap'
          exact ⟨v, rfl, hunwrap'⟩
    obtain ⟨v, hv, hunwrap⟩ := hstored
    have heq := reachability_of_loc_eq_resolve_reachability m fx v hv
    rw [heq, hunwrap]
    simp only [resolve_reachability]
    exact CapabilitySet.Subset.refl
  | poly T1 T2 =>
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf, cs, S0, t0, hresolve, hwf_cs, hR0_sub, hbody⟩ := ht
    refine ⟨hwf, cs, S0, t0, hresolve, hwf_cs, ?_, hbody⟩
    have hstored : ∃ v, m.heap fx = some (Cell.val v) ∧
        v.unwrap = Exp.tabs cs S0 t0 := by
      cases heq : m.heap fx with
      | none =>
        have hbad : (none : Option (Exp {})) = some (Exp.tabs cs S0 t0) := by
          simpa only [resolve, heq] using hresolve
        cases hbad
      | some cell =>
        cases cell with
        | capability =>
          have hbad : (none : Option (Exp {})) = some (Exp.tabs cs S0 t0) := by
            simpa only [resolve, heq] using hresolve
          cases hbad
        | masked =>
          have hbad : (none : Option (Exp {})) = some (Exp.tabs cs S0 t0) := by
            simpa only [resolve, heq] using hresolve
          cases hbad
        | val v =>
          have hunwrap : some v.unwrap = some (Exp.tabs cs S0 t0) := by
            simpa only [resolve, heq] using hresolve
          injection hunwrap with hunwrap'
          exact ⟨v, rfl, hunwrap'⟩
    obtain ⟨v, hv, hunwrap⟩ := hstored
    have heq := reachability_of_loc_eq_resolve_reachability m fx v hv
    rw [heq, hunwrap]
    simp only [resolve_reachability]
    exact CapabilitySet.Subset.refl
  | cpoly B T =>
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf, cs, B0, t0, hresolve, hwf_cs, hR0_sub, hbody⟩ := ht
    refine ⟨hwf, cs, B0, t0, hresolve, hwf_cs, ?_, hbody⟩
    have hstored : ∃ v, m.heap fx = some (Cell.val v) ∧
        v.unwrap = Exp.cabs cs B0 t0 := by
      cases heq : m.heap fx with
      | none =>
        have hbad : (none : Option (Exp {})) = some (Exp.cabs cs B0 t0) := by
          simpa only [resolve, heq] using hresolve
        cases hbad
      | some cell =>
        cases cell with
        | capability =>
          have hbad : (none : Option (Exp {})) = some (Exp.cabs cs B0 t0) := by
            simpa only [resolve, heq] using hresolve
          cases hbad
        | masked =>
          have hbad : (none : Option (Exp {})) = some (Exp.cabs cs B0 t0) := by
            simpa only [resolve, heq] using hresolve
          cases hbad
        | val v =>
          have hunwrap : some v.unwrap = some (Exp.cabs cs B0 t0) := by
            simpa only [resolve, heq] using hresolve
          injection hunwrap with hunwrap'
          exact ⟨v, rfl, hunwrap'⟩
    obtain ⟨v, hv, hunwrap⟩ := hstored
    have heq := reachability_of_loc_eq_resolve_reachability m fx v hv
    rw [heq, hunwrap]
    simp only [resolve_reachability]
    exact CapabilitySet.Subset.refl

/-- If the type environment is well-typed, then the denotation of any shape type is a
proper pre-denotation. -/
theorem shape_val_denot_is_proper {env : TypeEnv s} {S : Ty .shape s}
  (hts : EnvTyping Γ env k st m) :
  (Ty.shape_val_denot env S).is_proper := by
  refine ⟨shape_val_denot_is_reachability_safe (typed_env_is_reachability_safe hts) S,
    shape_val_denot_is_reachability_monotonic (typed_env_is_reachability_monotonic hts) S,
    shape_val_denot_implies_wf (typed_env_is_implying_wf hts) S,
    shape_val_denot_is_tight (typed_env_is_tight hts) S, ?_⟩
  intro C
  exact ⟨shape_val_denot_is_monotonic (typed_env_is_monotonic hts) S C,
    shape_val_denot_is_transparent (typed_env_is_transparent hts) S C,
    shape_val_denot_is_bool_independent (typed_env_is_bool_independent hts) S C,
    shape_val_denot_worldle_mono (typed_env_is_monotonic hts) S C,
    shape_val_denot_down_trunc (typed_env_is_downward_closed hts) S C⟩

/-- Capturing-type denotations entail heap well-formedness. -/
theorem capt_val_denot_implies_wf {env : TypeEnv s} (T : Ty .capt s)
    {k : Nat} {st : StoreTyping k} {m : Memory} {e : Exp {}}
    (h : Ty.capt_val_denot env T k st m e) : e.WfInHeap m.heap := by
  cases T with
  | capt C S =>
    simp only [Ty.capt_val_denot] at h
    exact h.2.1

/-- Capturing-type denotations entail simple-answer shape. -/
theorem capt_val_denot_implies_simple_ans {env : TypeEnv s} (T : Ty .capt s)
    {k : Nat} {st : StoreTyping k} {m : Memory} {e : Exp {}}
    (h : Ty.capt_val_denot env T k st m e) : e.IsSimpleAns := by
  cases T with
  | capt C S =>
    simp only [Ty.capt_val_denot] at h
    exact h.1

/-! ## Pack-witness bounds -/

theorem pack_bound_mono {R R' : CapabilitySet} {t : Trace} {v : Exp {}} {m' : Memory}
    (hsub : R ⊆ R') (h : pack_bound R t v m') : pack_bound R' t v m' :=
  fun cs fx heq => CapabilitySet.Subset.trans (h cs fx heq) (CapabilitySet.union_mono_left hsub)

theorem pack_bound_of_ne_pack {R : CapabilitySet} {t : Trace} {v : Exp {}} {m' : Memory}
    (h : ∀ cs fx, v ≠ .pack cs (.free fx)) : pack_bound R t v m' :=
  fun cs fx heq => absurd heq (h cs fx)

theorem CapabilitySet.ofList_append_subset {l1 l2 : List Nat} :
    CapabilitySet.ofList l1 ∪ CapabilitySet.ofList l2 ⊆ CapabilitySet.ofList (l1 ++ l2) := by
  apply CapabilitySet.subset_of_mem_transfer
  intro x hx
  rw [CapabilitySet.mem_ofList, List.mem_append]
  cases hx with
  | left h => exact Or.inl (CapabilitySet.mem_ofList.mp h)
  | right h => exact Or.inr (CapabilitySet.mem_ofList.mp h)

/-- A pack bound established with the head's allocations as extra authority yields a pack
bound for the concatenated trace. -/
theorem pack_bound_append {R : CapabilitySet} {t1 t2 : Trace} {v : Exp {}} {m' : Memory}
    (h : pack_bound (R ∪ CapabilitySet.ofList t1.allocList) t2 v m') :
    pack_bound R (t1 ++ t2) v m' := by
  intro cs fx heq
  refine CapabilitySet.Subset.trans (h cs fx heq) ?_
  rw [Trace.allocList_append]
  refine CapabilitySet.Subset.union_left ?_ ?_
  · refine CapabilitySet.Subset.union_left CapabilitySet.Subset.union_right_left ?_
    exact CapabilitySet.Subset.trans
      (CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left
        CapabilitySet.ofList_append_subset)
      CapabilitySet.Subset.union_right_right
  · exact CapabilitySet.Subset.trans
      (CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_right
        CapabilitySet.ofList_append_subset)
      CapabilitySet.Subset.union_right_right

/-! ## Properties of the expression relation -/

/-- At budget `0` nothing is owed. -/
theorem ExpDenot.zero {D : IDenot} {R : CapabilitySet} {st : StoreTyping 0} {m : Memory}
    {e : Exp {}} : ExpDenot D R 0 st m e :=
  fun _ => Eval.exhausted

/-- The expression relation is monotone in the authority. -/
theorem ExpDenot.mono_auth {D : IDenot} {R R' : CapabilitySet} {k : Nat} {st : StoreTyping k}
    {m : Memory} {e : Exp {}} (hsub : R ⊆ R') (h : ExpDenot D R k st m e) :
    ExpDenot D R' k st m e := by
  intro hmt
  refine eval_post_monotonic ?_ (Eval.mono_auth hsub (h hmt))
  intro t v m' _ hp hbud
  obtain ⟨st', hwle, hmt', hd, hpb⟩ := hp hbud
  exact ⟨st', hwle, hmt', hd, pack_bound_mono hsub hpb⟩

/-- The expression relation is covariant in the value denotation, along an index-uniform
implication at the starting world. -/
theorem ExpDenot.imply_after {D1 D2 : IDenot} {R : CapabilitySet} {k : Nat}
    {st : StoreTyping k} {m : Memory} {e : Exp {}}
    (himp : D1.ImplyAfter k st m D2) (h : ExpDenot D1 R k st m e) :
    ExpDenot D2 R k st m e := by
  intro hmt
  refine eval_post_monotonic ?_ (h hmt)
  intro t v m' _ hp hbud
  obtain ⟨st', hwle, hmt', hd, hpb⟩ := hp hbud
  exact ⟨st', hwle, hmt', himp _ (Nat.sub_le k t.readCount) st' m' hwle v hd, hpb⟩

/-- Equivalent value denotations give equivalent expression relations. -/
theorem ExpDenot.equiv {D1 D2 : IDenot} (heqv : D1 ≈ D2) {R : CapabilitySet} {k : Nat}
    {st : StoreTyping k} {m : Memory} {e : Exp {}} :
    ExpDenot D1 R k st m e ↔ ExpDenot D2 R k st m e :=
  ⟨ExpDenot.imply_after (IDenot.equiv_to_imply_after heqv k st m),
   ExpDenot.imply_after (IDenot.equiv_to_imply_after (IDenot.equiv_symm heqv) k st m)⟩

/-- Inversion of the expression relation on a variable: it yields the value denotation at
some well-typed future world at the same index. -/
theorem ExpDenot.var_inv {D : IDenot} {R : CapabilitySet} {k : Nat} {st : StoreTyping k}
    {m : Memory} {x : Var .var {}} (hkpos : 0 < k) (hmt : MemTyped k st m)
    (h : ExpDenot D R k st m (.var x)) :
    ∃ st' : StoreTyping k, WorldLe st' m st m ∧ MemTyped k st' m ∧ D k st' m (.var x) := by
  have hp := (h hmt).2 [] (.var x) m BigStep.bs_var
  simp only [ExpPost, Trace.readCount_nil, Nat.sub_zero, World.trunc_self] at hp
  obtain ⟨st', hwle, hmt', hd, _⟩ := hp hkpos
  exact ⟨st', hwle, hmt', hd⟩

/-! ## Store-typing preservation for the cell operations -/

/-- **Alloc preserves `MemTyped` and steps up `WorldLe`.** -/
theorem WT_alloc {k : Nat} {st : StoreTyping k} {m : Memory} {c : Nat}
    {R : MonRel k} {l : Nat} (hfresh : m.heap l = none) (hcontent : m.heap c ≠ none)
    (hwt : MemTyped k st m)
    (hRstable : ∀ (i : Fin k) (w1 w2 : StoreTyping i.val) (m1 m2 : Memory),
      WorldLe w2 m2 w1 m1 → ∀ e, R i w1 m1 e → R i w2 m2 e)
    (hRext : ∀ (i : Fin k),
      R i ((st.set l R).trunc (Nat.le_of_lt i.isLt)) (m.extend_mcell l c hfresh hcontent)
        (.var (.free c))) :
    WorldLe (st.set l R) (m.extend_mcell l c hfresh hcontent) st m ∧
      MemTyped k (st.set l R) (m.extend_mcell l c hfresh hcontent) := by
  obtain ⟨hcons, hstable, hgood⟩ := hwt
  have hsub : (m.extend_mcell l c hfresh hcontent).subsumes m :=
    Memory.extend_mcell_subsumes m l c hfresh hcontent
  have hstfresh : st.lookup l = none := by
    rcases hopt : st.lookup l with _ | R0
    · rfl
    · obtain ⟨n, hlk⟩ := hcons l R0 hopt
      rw [show m.lookup l = m.heap l from rfl] at hlk
      rw [hfresh] at hlk; cases hlk
  have hwle : WorldLe (st.set l R) (m.extend_mcell l c hfresh hcontent) st m := by
    refine ⟨hsub, ?_⟩
    intro l' R' h
    rw [World.set_lookup]
    by_cases hl' : l' = l
    · subst hl'; rw [hstfresh] at h; cases h
    · rw [if_neg hl']; exact h
  refine ⟨hwle, ?_, ?_, ?_⟩
  · intro l' R' hst'
    rw [World.set_lookup] at hst'
    by_cases hl' : l' = l
    · subst hl'; exact ⟨c, Memory.extend_mcell_lookup hfresh hcontent⟩
    · rw [if_neg hl'] at hst'
      obtain ⟨n, hlk⟩ := hcons l' R' hst'
      refine ⟨n, ?_⟩
      rw [Memory.extend_mcell_lookup_ne hfresh hcontent hl']
      exact hlk
  · intro l' R' hst'
    rw [World.set_lookup] at hst'
    by_cases hl' : l' = l
    · subst l'; rw [if_pos rfl] at hst'; obtain rfl := Option.some.inj hst'; exact hRstable
    · rw [if_neg hl'] at hst'; exact hstable l' R' hst'
  · intro l' n R' hst' hlk' i
    rw [World.set_lookup] at hst'
    by_cases hl' : l' = l
    · subst l'
      rw [if_pos rfl] at hst'
      obtain rfl := Option.some.inj hst'
      have hcn : c = n := by
        have hlc := Memory.extend_mcell_lookup (m := m) (l := l) (n := c) hfresh hcontent
        have hinj := Option.some.inj (hlc.symm.trans hlk')
        exact CapabilityInfo.mcell.inj (Cell.capability.inj hinj)
      subst hcn
      exact hRext i
    · rw [if_neg hl'] at hst'
      have hlk_old : m.lookup l' = some (.capability (.mcell n)) := by
        rw [← hlk']
        exact (Memory.extend_mcell_lookup_ne hfresh hcontent hl').symm
      have hgv := hgood l' n R' hst' hlk_old i
      exact hstable l' R' hst' i _ _ _ _ (WorldLe.trunc (Nat.le_of_lt i.isLt) hwle) _ hgv

/-- **Write preserves `MemTyped`** (store typing fixed; memory updated type-preservingly). -/
theorem WT_write {k : Nat} {st : StoreTyping k} {m : Memory} {l : Nat}
    {R : MonRel k} {y n0 : Nat}
    (hexists : m.lookup l = some (.capability (.mcell n0)))
    (hcontent : m.heap y ≠ none)
    (hst : st.lookup l = some R) (hwt : MemTyped k st m)
    (hyR : ∀ (i : Fin k),
      R i (st.trunc (Nat.le_of_lt i.isLt)) (m.update_mcell l y ⟨n0, hexists⟩ hcontent)
        (.var (.free y))) :
    WorldLe st (m.update_mcell l y ⟨n0, hexists⟩ hcontent) st m ∧
      MemTyped k st (m.update_mcell l y ⟨n0, hexists⟩ hcontent) := by
  obtain ⟨hcons, hstable, hgood⟩ := hwt
  have hsub : (m.update_mcell l y ⟨n0, hexists⟩ hcontent).subsumes m :=
    Memory.update_mcell_subsumes m l y ⟨n0, hexists⟩ hcontent
  refine ⟨WorldLe.of_subsumes hsub, ?_, hstable, ?_⟩
  · intro l' R' hst'
    obtain ⟨n, hlk⟩ := hcons l' R' hst'
    by_cases hl' : l' = l
    · subst hl'
      exact ⟨y, Memory.update_mcell_lookup ⟨n0, hexists⟩ hcontent⟩
    · refine ⟨n, ?_⟩
      rw [Memory.update_mcell_lookup_ne ⟨n0, hexists⟩ hcontent hl']
      exact hlk
  · intro l' n R' hst' hlk' i
    by_cases hl' : l' = l
    · subst l'
      rw [hst] at hst'
      obtain rfl := Option.some.inj hst'
      have hyn : y = n := by
        have hlu := Memory.update_mcell_lookup (m := m) (l := l) (n := y) ⟨n0, hexists⟩ hcontent
        have hinj := Option.some.inj (hlu.symm.trans hlk')
        exact CapabilityInfo.mcell.inj (Cell.capability.inj hinj)
      subst hyn
      exact hyR i
    · have hlk_old : m.lookup l' = some (.capability (.mcell n)) := by
        rw [← hlk']
        exact (Memory.update_mcell_lookup_ne ⟨n0, hexists⟩ hcontent hl').symm
      have hgv := hgood l' n R' hst' hlk_old i
      exact hstable l' R' hst' i _ _ _ _
        (WorldLe.trunc (Nat.le_of_lt i.isLt) (WorldLe.of_subsumes hsub)) _ hgv

/-- **Binding a value preserves `MemTyped`** (the store typing is unchanged; the new
location is not a cell). -/
theorem WT_extend_val {k : Nat} {st : StoreTyping k} {m : Memory} {l : Nat} {w : HeapVal}
    (hwf_v : Exp.WfInHeap w.unwrap m.heap)
    (hreach : w.reachability = compute_reachability m.heap w.unwrap w.isVal)
    (hfresh : m.heap l = none)
    (hwt : MemTyped k st m) :
    MemTyped k st (m.extend_val l w hwf_v hreach hfresh) := by
  obtain ⟨hcons, hstable, hgood⟩ := hwt
  have hsub : (m.extend_val l w hwf_v hreach hfresh).subsumes m :=
    Memory.extend_val_subsumes m l w hwf_v hreach hfresh
  have hne : ∀ {l' : Nat} {R : MonRel k}, st.lookup l' = some R → l' ≠ l := by
    rintro l' R hst' rfl
    obtain ⟨n, hlk⟩ := hcons l' R hst'
    simp [Memory.lookup, hfresh] at hlk
  refine ⟨?_, hstable, ?_⟩
  · intro l' R' hst'
    obtain ⟨n, hlk⟩ := hcons l' R' hst'
    refine ⟨n, ?_⟩
    rw [show (m.extend_val l w hwf_v hreach hfresh).lookup l' = m.lookup l' from by
      simp only [Memory.lookup, Memory.extend_val, Heap.extend, if_neg (hne hst')]]
    exact hlk
  · intro l' n R' hst' hlk' i
    have hl'ne : l' ≠ l := hne hst'
    have hlk_old : m.lookup l' = some (.capability (.mcell n)) := by
      rw [← hlk']
      simp only [Memory.lookup, Memory.extend_val, Heap.extend, if_neg hl'ne]
    have hgv := hgood l' n R' hst' hlk_old i
    exact hstable l' R' hst' i _ _ _ _
      (WorldLe.trunc (Nat.le_of_lt i.isLt) (WorldLe.of_subsumes hsub)) _ hgv


/-! ## Introduction of the expression relation at answers -/

theorem pack_bound_of_simple {R : CapabilitySet} {t : Trace} {v : Exp {}} {m' : Memory}
    (hv : v.IsSimpleVal) : pack_bound R t v m' :=
  fun _ _ heq => by subst heq; cases hv

theorem pack_bound_of_var {R : CapabilitySet} {t : Trace} {x : Var .var {}} {m' : Memory} :
    pack_bound R t (.var x) m' :=
  fun _ _ heq => by cases heq

theorem pack_bound_pack {R : CapabilitySet} {t : Trace} {cs : CaptureSet {}} {fx : Nat}
    {m' : Memory} (h : reachability_of_loc m'.heap fx ⊆ R) :
    pack_bound R t (.pack cs (.free fx)) m' := by
  intro cs' fx' heq
  injection heq with _ _ heq'
  injection heq' with _ _ heq'
  subst heq'
  exact CapabilitySet.Subset.trans h CapabilitySet.Subset.union_right_left

/-- An answer satisfies the expression relation as soon as it satisfies the value
denotation at some well-typed future world of the starting world (same index). -/
theorem ExpDenot.ans_intro {D : IDenot} {R : CapabilitySet} {k : Nat} {st : StoreTyping k}
    {m : Memory} {v : Exp {}} (hans : v.IsAns) (hpb : pack_bound R [] v m)
    (hd : MemTyped k st m →
      ∃ st' : StoreTyping k, WorldLe st' m st m ∧ MemTyped k st' m ∧ D k st' m v) :
    ExpDenot D R k st m v := by
  intro hmt
  refine ⟨Safe.ans hans, ?_⟩
  intro t v' m' hbs
  obtain ⟨rfl, rfl, rfl⟩ := BigStep.isAns_inv hbs hans
  simp only [ExpPost, Trace.readCount_nil, Nat.sub_zero, World.trunc_self]
  intro _
  obtain ⟨st', hwle, hmt', hd'⟩ := hd hmt
  exact ⟨st', hwle, hmt', hd', hpb⟩

/-- An answer satisfies the expression relation when it satisfies the value denotation at
the starting world. -/
theorem ExpDenot.ans_intro_same {D : IDenot} {R : CapabilitySet} {k : Nat}
    {st : StoreTyping k} {m : Memory} {v : Exp {}} (hans : v.IsAns) (hpb : pack_bound R [] v m)
    (hd : MemTyped k st m → D k st m v) : ExpDenot D R k st m v :=
  ExpDenot.ans_intro hans hpb (fun hmt => ⟨st, WorldLe.refl st m, hmt, hd hmt⟩)

/-- `unit` is a `unit`-value at every world. -/
theorem unit_val_denot (env : TypeEnv s) (k : Nat) (st : StoreTyping k) (m : Memory) :
    Ty.exi_val_denot env (.typ (.capt {} .unit)) k st m .unit := by
  simp only [Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  exact ⟨.is_simple_val .unit, .wf_unit, by simp only [CaptureSet.subst]; exact .wf_empty,
    by simp [resolve]⟩

theorem btrue_val_denot (env : TypeEnv s) (k : Nat) (st : StoreTyping k) (m : Memory) :
    Ty.exi_val_denot env (.typ (.capt {} .bool)) k st m .btrue := by
  simp only [Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  exact ⟨.is_simple_val .btrue, .wf_btrue, by simp only [CaptureSet.subst]; exact .wf_empty,
    by simp [resolve]⟩

theorem bfalse_val_denot (env : TypeEnv s) (k : Nat) (st : StoreTyping k) (m : Memory) :
    Ty.exi_val_denot env (.typ (.capt {} .bool)) k st m .bfalse := by
  simp only [Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  exact ⟨.is_simple_val .bfalse, .wf_bfalse, by simp only [CaptureSet.subst]; exact .wf_empty,
    by simp [resolve]⟩


/-- The postcondition of the expression relation after a single non-read event: the
index is unchanged (definitionally), so a same-index future world suffices. -/
theorem ExpPost.access_intro {k : Nat} {st : StoreTyping k} {m : Memory} {R : CapabilitySet}
    {D : IDenot} {l : Nat} {v : Exp {}} {m' : Memory}
    (st' : StoreTyping k) (hwle : WorldLe st' m' st m) (hmt' : MemTyped k st' m')
    (hd : D k st' m' v) (hpb : pack_bound R [.access l] v m') :
    ExpPost k st m R D [.access l] v m' := by
  intro _
  refine ⟨st', ?_, hmt', hd, hpb⟩
  rw [show st.trunc (Nat.sub_le k (Trace.readCount [TraceItem.access l])) = st from
    World.trunc_self _ st]
  exact hwle

theorem ExpPost.alloc_intro {k : Nat} {st : StoreTyping k} {m : Memory} {R : CapabilitySet}
    {D : IDenot} {l : Nat} {v : Exp {}} {m' : Memory}
    (st' : StoreTyping k) (hwle : WorldLe st' m' st m) (hmt' : MemTyped k st' m')
    (hd : D k st' m' v) (hpb : pack_bound R [.alloc l] v m') :
    ExpPost k st m R D [.alloc l] v m' := by
  intro _
  refine ⟨st', ?_, hmt', hd, hpb⟩
  rw [show st.trunc (Nat.sub_le k (Trace.readCount [TraceItem.alloc l])) = st from
    World.trunc_self _ st]
  exact hwle

/-- The postcondition of the expression relation after a single read: the index drops by
one and the world is truncated accordingly. -/
theorem ExpPost.read_intro {k : Nat} {st : StoreTyping k} {m : Memory} {R : CapabilitySet}
    {D : IDenot} {l : Nat} {v : Exp {}} {m' : Memory}
    (st' : StoreTyping k) (hwle : WorldLe st' m' st m) (hmt' : MemTyped k st' m')
    (hd : k - 1 < k → D (k - 1) (st'.trunc (Nat.sub_le k 1)) m' v)
    (hpb : pack_bound R [.read l] v m') :
    ExpPost k st m R D [.read l] v m' := by
  intro hbud
  have hpred : k - 1 < k := by
    simp only [Trace.readCount_read, Trace.readCount_nil, Nat.zero_add] at hbud
    omega
  exact ⟨st'.trunc (Nat.sub_le k 1), WorldLe.trunc (Nat.sub_le k 1) hwle,
    MemTyped_trunc (Nat.sub_le k 1) hmt', hd hpred, hpb⟩

end CC
