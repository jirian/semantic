import Semantic.CC.Fundamental
import Semantic.CC.Semantics.Props
namespace CC

/-! The following defines _platforms_. -/

/-- Context signature of a platform of `n` ground capabilities. -/
def Sig.platform_of : Nat -> Sig
| 0 => {}
| n+1 => ((Sig.platform_of n),C),x

/-- A platform context with `n` ground capabilities. -/
def Ctx.platform_of : (n : Nat) -> Ctx (Sig.platform_of n)
| 0 => .empty
| n+1 => ((Ctx.platform_of n),C<:.unbound),x:(.capt (.cvar .here) .cap)

/-- A platform heap with `n` ground capabilities (basic capabilities). -/
def Heap.platform_of (N : Nat) : Heap :=
  fun i =>
    if i < N then
      .some (.capability .basic)
    else
      .none

/-- The size of a signature. -/
def Sig.size : Sig -> Nat :=
  fun s => s.length

/-- Debruijn-level of a bound variable. -/
def BVar.level : BVar s k -> Nat
| .here => by
  rename_i s0
  exact s0.size
| .there x => x.level

/-- Convert a capture set in a platform context to a concrete capability set.
  Platform contexts have `N` capabilities arranged as pairs `(C, x)` at levels
  `(0,1), (2,3), ..., (2N-2, 2N-1)`, where capability `i` corresponds to
  variables at levels `2i` and `2i+1`. Bound variables map via `level / 2`,
  while free variables directly reference heap locations. -/
def CaptureSet.to_platform_capability_set : CaptureSet (Sig.platform_of N) -> CapabilitySet
| .empty => .empty
| .union cs1 cs2 =>
    (cs1.to_platform_capability_set) ∪ (cs2.to_platform_capability_set)
| .var x =>
    match x with
    | .bound b => .cap (b.level / 2)
    | .free n => .cap n
| .cvar c => .cap (c.level / 2)

/-- Type environment for a platform with `N` ground capabilities.
  Maps each pair `(C, x)` to capability `i` at heap location `i`:
  capture variable `C` maps to singleton ground capture set `{i}`,
  term variable `x` maps to heap location `i`. -/
def TypeEnv.platform_of : (N : Nat) -> TypeEnv (Sig.platform_of N)
| 0 => .empty
| N+1 => ((TypeEnv.platform_of N).extend_cvar (.var (.free N))).extend_var N

/-- The platform heap is well-formed: it contains only capabilities, no values. -/
theorem Heap.platform_of_wf (N : Nat) : (Heap.platform_of N).WfHeap := by
  constructor
  · -- wf_val: no values in the platform heap
    intro l hv hlookup
    unfold Heap.platform_of at hlookup
    split at hlookup <;> cases hlookup
  · -- wf_reach: no values in the platform heap
    intro l v hv R hlookup
    unfold Heap.platform_of at hlookup
    split at hlookup <;> cases hlookup

/-- The platform heap has finite domain {0, 1, ..., N-1}. -/
theorem Heap.platform_of_has_fin_dom (N : Nat) :
  (Heap.platform_of N).HasFinDom (Finset.range N) := by
  intro l
  unfold Heap.platform_of
  constructor
  · -- If heap is not none, then l < N
    intro h
    split at h
    case isTrue hlt =>
      simp [Finset.mem_range, hlt]
    case isFalse =>
      contradiction
  · -- If l ∈ range N, then heap is not none
    intro h
    simp [Finset.mem_range] at h
    split
    case isTrue => simp
    case isFalse hf => omega

/-- Platform memory with `N` ground capabilities. The platform holds no mutable cells,
  so the content-closure invariant `mcell_wf` is vacuous. -/
def Memory.platform_of (N : Nat) : Memory where
  heap := Heap.platform_of N
  wf := Heap.platform_of_wf N
  findom := ⟨Finset.range N, Heap.platform_of_has_fin_dom N⟩
  mcell_wf := by
    intro l n hlookup
    unfold Heap.platform_of at hlookup
    split at hlookup <;> cases hlookup

/-- Platform memory M subsumes platform memory N when M ≥ N. -/
theorem platform_memory_subsumes {N M : Nat} (hNM : N ≤ M) :
  (Memory.platform_of M).subsumes (Memory.platform_of N) := by
  intro l v hlookup
  unfold Memory.platform_of Heap.platform_of at hlookup ⊢
  simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hlookup
  obtain ⟨hlN, rfl⟩ := hlookup
  refine ⟨.capability .basic, ?_, Cell.subsumes_refl _⟩
  simp only [if_pos (by omega : l < M)]

/-- EnvTyping for platform is monotonic in the memory (at a fixed budget/world): platform
  `N` types in platform `M` memory when `M ≥ N`. -/
theorem env_typing_platform_monotonic {Γ : Ctx s} {env : TypeEnv s} {N M k : Nat}
  {st : StoreTyping k}
  (hNM : N ≤ M)
  (ht : EnvTyping Γ env k st (Memory.platform_of N)) :
  EnvTyping Γ env k st (Memory.platform_of M) :=
  env_typing_monotonic ht (platform_memory_subsumes hNM)

/-- Lookup of a platform capability location. -/
theorem Heap.platform_of_lookup {N l : Nat} (hl : l < N) :
  Heap.platform_of N l = some (.capability .basic) := by
  unfold Heap.platform_of
  rw [if_pos hl]

/-- The platform environment types against the platform memory at any budget and any
  store typing: the platform holds only basic capabilities, whose denotations are
  world-independent. -/
theorem env_typing_of_platform {N k : Nat} {st : StoreTyping k} :
  EnvTyping
    (Ctx.platform_of N)
    (TypeEnv.platform_of N)
    k st
    (Memory.platform_of N) := by
  induction N with
  | zero =>
    unfold Ctx.platform_of TypeEnv.platform_of
    exact True.intro
  | succ N ih =>
    unfold Ctx.platform_of TypeEnv.platform_of EnvTyping
    simp only [List.empty_eq]
    have hlk : Heap.platform_of (N + 1) N = some (.capability .basic) :=
      Heap.platform_of_lookup (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- Term variable x : .capt (.cvar .here) .cap at location N
      rw [capt_val_denot_capt]
      refine ⟨Exp.IsSimpleAns.is_var, ?_, ?_, ?_⟩
      · exact Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hlk)
      · simp only [CaptureSet.subst, Subst.from_TypeEnv]
        change CaptureSet.WfInHeap (CaptureSet.var (Var.free N)) _
        exact CaptureSet.WfInHeap.wf_var_free hlk
      · change Ty.shape_val_denot _ Ty.cap _ _ _ _ _
        simp only [Ty.shape_val_denot]
        refine ⟨Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hlk), N, rfl, hlk, ?_⟩
        change N ∈ (CaptureSet.var (Var.free N)).ground_denot (Memory.platform_of (N + 1))
        change N ∈ reachability_of_loc (Heap.platform_of (N + 1)) N
        unfold reachability_of_loc
        rw [hlk]
        exact CapabilitySet.mem.here
    · exact CaptureSet.WfInHeap.wf_var_free hlk
    · change CaptureBound.WfInHeap .unbound (Memory.platform_of (N + 1)).heap
      exact CaptureBound.WfInHeap.wf_unbound
    · exact CapabilitySet.BoundedBy.top
    · exact env_typing_platform_monotonic (N := N) (M := N + 1) (by omega) ih

/-! # Adequacy: semantic typing implies safety

A configuration `(m, e)` is _safe_ under authority `A` when every partial run
from it (a `Reduce` with trace `t`) ends in a progressive configuration (an
answer, or one that can take a further step), and its trace is authorized by
`A`: every read/write hits a capability in `A` or a cell the run itself
allocated (`TraceOk`).

Semantically well-typed expressions are safe under the authority denoted by
their use set.  Semantic typing is budget-indexed: given a partial run with
trace `t`, we instantiate it at read budget `t.readCount + 1`, so the run is
strictly within budget and the `Safe` derivation can be consulted along it. -/

def Exp.Safe (A : CapabilitySet) (m : Memory) (e : Exp {}) : Prop :=
  ∀ t m' e',
    Reduce t m e m' e' ->
    IsProgressive m' e' ∧ TraceOk t A

/-- Safety is monotone in the authority. -/
theorem Exp.Safe.mono
  (hsafe : Exp.Safe A m e)
  (hsub : A ⊆ A') :
  Exp.Safe A' m e := by
  intro t m' e' hred
  obtain ⟨hprog, hok⟩ := hsafe t m' e' hred
  exact ⟨hprog, TraceOk.mono hsub hok⟩

/-- A configuration with an evaluation at every budget is safe. -/
theorem eval_implies_safe
  (heval : ∀ k, ∃ Q, Eval k A m e Q) :
  Exp.Safe A m e := by
  intro t m' e' hred
  obtain ⟨Q, hev⟩ := heval (t.readCount + 1)
  exact ⟨safe_reduce_progressive hev.1 hred (by omega),
    safe_reduce_traceok hev.1 hred (by omega)⟩

/-- Adequacy of semantic typing: a semantically well-typed expression, closed by
  an environment typed in a memory against a family of well-typed store typings
  (one per budget), is safe in that memory under the authority denoted by its
  use set. -/
theorem adequacy
  (ht : C # Γ ⊨ e : E)
  (st : (k : Nat) -> StoreTyping k)
  (hts : ∀ k, EnvTyping Γ env k (st k) m)
  (hmt : ∀ k, MemTyped k (st k) m) :
  Exp.Safe (C.denot env m) m (e.subst (Subst.from_TypeEnv env)) := by
  apply eval_implies_safe
  intro k
  have heval := ht env k (st k) m (hts k)
  simp only [Ty.exi_exp_denot] at heval
  exact ⟨_, heval (hmt k)⟩

/-- A closed ground capture set denotes the empty authority. -/
theorem CaptureSet.ground_denot_of_closed {cs : CaptureSet {}}
  (hclosed : cs.IsClosed) (m : Memory) :
  cs.ground_denot m ⊆ {} := by
  induction hclosed with
  | empty => exact CapabilitySet.subset_refl
  | union _ _ ih1 ih2 => exact CapabilitySet.union_subset_of_subset_of_subset ih1 ih2
  | cvar => rename_i x; cases x
  | var_bound => rename_i x; cases x

/-- A closed capture set in the empty environment denotes the empty authority. -/
theorem CaptureSet.denot_empty_of_closed {cs : CaptureSet {}}
  (hclosed : cs.IsClosed) (m : Memory) :
  cs.denot .empty m ⊆ {} := by
  unfold CaptureSet.denot
  rw [Subst.from_TypeEnv_empty, CaptureSet.subst_id]
  exact CaptureSet.ground_denot_of_closed hclosed _

/-- Adequacy for closed expressions: a closed semantically well-typed expression
  with a closed use set is safe in the empty memory under the empty authority.
  The empty store typing is well-typed for every memory (`MemTyped_empty`). -/
theorem adequacy_closed {e : Exp {}}
  (ht : C # Ctx.empty ⊨ e : E)
  (hclosed : C.IsClosed) :
  Exp.Safe {} Memory.empty e := by
  have hsafe := adequacy ht (env := .empty) (m := Memory.empty) World.empty
    (fun _ => True.intro) (fun k => MemTyped_empty k _)
  rw [Subst.from_TypeEnv_empty, Exp.subst_id] at hsafe
  exact hsafe.mono (CaptureSet.denot_empty_of_closed hclosed _)

/-- Type soundness for closed expressions: syntactic typing implies safety
  in the empty memory under the empty authority. -/
theorem soundness {e : Exp {}}
  (ht : C # Ctx.empty ⊢ e : T) :
  Exp.Safe {} Memory.empty e :=
  adequacy_closed (fundamental ht) (HasType.use_set_is_closed ht)

/-- Progress for closed expressions: every configuration reachable from a
  closed well-typed expression is progressive. -/
theorem soundness_progress {e : Exp {}}
  (ht : C # Ctx.empty ⊢ e : T)
  (hred : Reduce t Memory.empty e m' e') :
  IsProgressive m' e' :=
  (soundness ht t m' e' hred).1

/-- Capability soundness for closed expressions: a closed well-typed expression
  only ever accesses cells it allocated itself when reduced in the empty memory. -/
theorem soundness_capability {e : Exp {}}
  (ht : C # Ctx.empty ⊢ e : T)
  (hred : Reduce t Memory.empty e m' e') :
  TraceOk t {} :=
  (soundness ht t m' e' hred).2

/-! ## Safety on platforms

A _platform_ provides `N` ground capabilities. Closed programs typed in a
platform context are safe when run on the corresponding platform memory. -/

/-- An expression is safe with platform `N` under authority `P` when it is
  safe in the platform memory with `N` ground capabilities. -/
def Exp.SafeWithPlatform (e : Exp {}) (N : Nat) (P : CapabilitySet) : Prop :=
  Exp.Safe P (Memory.platform_of N) e

/-- Reachability of a location in platform heap is just the singleton set. -/
theorem reachability_of_loc_platform {l : Nat} (hl : l < N) :
  reachability_of_loc (Heap.platform_of N) l = {l} := by
  unfold reachability_of_loc Heap.platform_of
  simp [hl]

/-- The length of a platform signature is 2*N. -/
theorem Sig.platform_of_length : (Sig.platform_of N).length = 2 * N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    unfold Sig.platform_of Sig.extend_cvar Sig.extend_var
    simp only [List.length]
    rw [ih]
    omega

/-- Lookup of term variable in platform environment. -/
theorem TypeEnv.lookup_var_platform {x : BVar (Sig.platform_of N) .var} :
  (TypeEnv.platform_of N).lookup_var x = x.level / 2 := by
  induction N with
  | zero => cases x
  | succ N ih =>
    cases x with
    | here =>
      change N = (Sig.platform_of N,C).length / 2
      unfold Sig.extend_cvar
      simp only [List.length]
      rw [Sig.platform_of_length]
      omega
    | there x' =>
      cases x' with
      | there x'' =>
        change (TypeEnv.platform_of N).lookup_var x'' = x''.level / 2
        exact ih

theorem TypeEnv.lookup_cvar_platform {c : BVar (Sig.platform_of N) .cvar} :
  (TypeEnv.platform_of N).lookup_cvar c = .var (.free (c.level / 2)) := by
  induction N with
  | zero => cases c
  | succ N ih =>
    cases c with
    | there c' =>
      cases c' with
      | here =>
        change CaptureSet.var (Var.free N) =
          CaptureSet.var (Var.free ((Sig.platform_of N).length / 2))
        rw [Sig.platform_of_length]
        congr 2
        omega
      | there c'' =>
        change (TypeEnv.platform_of N).lookup_cvar c'' =
          CaptureSet.var (Var.free (c''.level / 2))
        exact ih

theorem BVar.level_var_bound {b : BVar (Sig.platform_of N) .var} : b.level / 2 < N := by
  induction N with
  | zero => cases b
  | succ N ih =>
    cases b with
    | here =>
      unfold BVar.level Sig.size Sig.extend_cvar
      simp only [List.length]
      rw [Sig.platform_of_length]
      omega
    | there b' =>
      cases b' with
      | there b'' =>
        simp only [BVar.level]
        have := ih (b := b'')
        omega

/-- For any bound capture variable in a platform signature,
    its level divided by 2 is less than N. -/
theorem BVar.level_cvar_bound {c : BVar (Sig.platform_of N) .cvar} : c.level / 2 < N := by
  induction N with
  | zero => cases c
  | succ N ih =>
    cases c with
    | there c' =>
      cases c' with
      | here =>
        simp only [BVar.level, Sig.size]
        rw [Sig.platform_of_length]
        omega
      | there c'' =>
        simp only [BVar.level]
        have := ih (c := c'')
        omega

/-- The denotation of a capture set in the platform environment equals
    its direct capability set translation, provided the capture set is well-formed. -/
theorem capture_set_denot_eq_platform {C : CaptureSet (Sig.platform_of N)}
  (hwf : C.WfInHeap (Heap.platform_of N)) :
  C.denot (TypeEnv.platform_of N) (Memory.platform_of N) = C.to_platform_capability_set := by
  unfold CaptureSet.denot
  induction C with
  | empty =>
    unfold CaptureSet.subst CaptureSet.ground_denot CaptureSet.to_platform_capability_set
    rfl
  | union cs1 cs2 ih1 ih2 =>
    cases hwf with
    | wf_union hwf1 hwf2 =>
      unfold CaptureSet.subst CaptureSet.to_platform_capability_set CaptureSet.ground_denot
      unfold CaptureSet.denot at ih1 ih2
      rw [ih1 hwf1, ih2 hwf2]
  | var x =>
    unfold CaptureSet.subst CaptureSet.to_platform_capability_set
    cases x with
    | bound b =>
      unfold Subst.from_TypeEnv Var.subst
      simp only [CaptureSet.ground_denot]
      rw [TypeEnv.lookup_var_platform]
      have hlevel : b.level / 2 < N := BVar.level_var_bound
      change reachability_of_loc (Heap.platform_of N) (b.level / 2) =
        CapabilitySet.cap (b.level / 2)
      rw [reachability_of_loc_platform hlevel]
      rfl
    | free n =>
      cases hwf with
      | wf_var_free hlookup =>
        unfold Subst.from_TypeEnv Var.subst
        simp only [CaptureSet.ground_denot]
        change reachability_of_loc (Heap.platform_of N) n = CapabilitySet.cap n
        have hn : n < N := by
          unfold Heap.platform_of at hlookup
          split at hlookup
          case isTrue h => exact h
          case isFalse => contradiction
        rw [reachability_of_loc_platform hn]
        rfl
  | cvar c =>
    unfold CaptureSet.subst CaptureSet.to_platform_capability_set
    simp only [Subst.from_TypeEnv]
    rw [TypeEnv.lookup_cvar_platform]
    unfold CaptureSet.ground_denot Memory.platform_of
    have hlevel : c.level / 2 < N := BVar.level_cvar_bound
    rw [reachability_of_loc_platform hlevel]
    rfl

/-- Adequacy of semantic typing on platform contexts: a closed program typed
  in a platform context is safe on the corresponding platform memory under the
  authority given by its (closed) use set.  The platform holds no mutable cells,
  so the empty store typing suffices at every budget. -/
theorem adequacy_platform {e : Exp (Sig.platform_of N)}
  (ht : C # Ctx.platform_of N ⊨ e : E)
  (hclosed : C.IsClosed) :
  (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))).SafeWithPlatform
    N
    (C.to_platform_capability_set) := by
  have hsafe := adequacy ht World.empty (fun _ => env_typing_of_platform)
    (fun k => MemTyped_empty k _)
  rwa [capture_set_denot_eq_platform (CaptureSet.wf_of_closed hclosed)] at hsafe

/-- Type soundness on platform contexts: a syntactically well-typed program in a
  platform context is safe on the corresponding platform memory. -/
theorem soundness_platform {e : Exp (Sig.platform_of N)}
  (ht : C # Ctx.platform_of N ⊢ e : T) :
  (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))).SafeWithPlatform
    N
    (C.to_platform_capability_set) :=
  adequacy_platform (fundamental ht) (HasType.use_set_is_closed ht)

/-- Capability soundness on platform contexts: reductions of a syntactically
  well-typed program in a platform context only access the platform capabilities
  in its use set, or cells the run allocated itself. -/
theorem soundness_platform_capability {e : Exp (Sig.platform_of N)}
  (ht : C # Ctx.platform_of N ⊢ e : T)
  (hred : Reduce t (Memory.platform_of N)
    (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))) m' e') :
  TraceOk t C.to_platform_capability_set :=
  (soundness_platform ht t m' e' hred).2

end CC
