import Semantic.CC.Syntax
import Semantic.CC.Substitution
import Semantic.CC.Semantics.Heap
import Semantic.CC.Semantics.Trace
import Semantic.CC.Semantics.SmallStep

/-!
# Big-step semantics and budget-indexed safety

The logical relation is built on a relational big-step semantics `BigStep` that records
the trace of heap events of a run, together with a *safety* predicate `Safe k R m e`
indexed by a read budget `k` (the step index of the model) and an authority `R` (the
capabilities the run may use).  `Eval k R m e Q` bundles safety with a postcondition on
all big-step runs.
-/

namespace CC

/-- Trace-observing postcondition: a predicate on the trace, the answer, and the final
  memory of a run. -/
def Tpost := Trace -> Exp {} -> Memory -> Prop

/-- Entailment between trace postconditions. -/
def Tpost.entails (Q1 Q2 : Tpost) : Prop :=
  ∀ t e m, Q1 t e m -> Q2 t e m

theorem Tpost.entails_refl (Q : Tpost) : Q.entails Q := fun _ _ _ h => h

/-- Relational big-step evaluation `BigStep m e t v m'`: `e` in memory `m` runs to the
  answer `v` in memory `m'`, emitting the trace `t`. -/
inductive BigStep : Memory -> Exp {} -> Trace -> Exp {} -> Memory -> Prop where
| bs_pack {m : Memory} {cs : CaptureSet {}} {x : Var .var {}} :
  BigStep m (.pack cs x) [] (.pack cs x) m
| bs_val {m : Memory} {v : Exp {}} :
  (hv : Exp.IsSimpleVal v) ->
  BigStep m v [] v m
| bs_var {m : Memory} {x : Var .var {}} :
  BigStep m (.var x) [] (.var x) m
| bs_apply {m : Memory} {x y : Nat} :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  BigStep m (e.subst (Subst.openVar (.free y))) t v m' ->
  BigStep m (.app (.free x) (.free y)) t v m'
| bs_invoke {m : Memory} {x y : Nat} :
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  BigStep m (.app (.free x) (.free y)) [.access x] .unit m
| bs_tapply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.tabs cs T0 e, hv, R⟩) ->
  BigStep m (e.subst (Subst.openTVar .top)) t v m' ->
  BigStep m (.tapp (.free x) S) t v m'
| bs_capply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.cabs cs B0 e, hv, R⟩) ->
  BigStep m (e.subst (Subst.openCVar CS)) t v m' ->
  BigStep m (.capp (.free x) CS) t v m'
| bs_letin_val {m m1 m2 : Memory} {v : Exp {}} {l' : Nat} :
  BigStep m e1 t1 v m1 ->
  (hv : Exp.IsSimpleVal v) ->
  (hwf_v : Exp.WfInHeap v m1.heap) ->
  (hfresh : m1.lookup l' = none) ->
  BigStep (m1.extend_val l' ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh)
    (e2.subst (Subst.openVar (.free l'))) t2 v2 m2 ->
  BigStep m (.letin e1 e2) (t1 ++ t2) v2 m2
| bs_letin_var {m m1 m2 : Memory} {x : Var .var {}} :
  BigStep m e1 t1 (.var x) m1 ->
  BigStep m1 (e2.subst (Subst.openVar x)) t2 v2 m2 ->
  BigStep m (.letin e1 e2) (t1 ++ t2) v2 m2
| bs_unpack {m m1 m2 : Memory} {x : Var .var {}} {cs : CaptureSet {}} :
  BigStep m e1 t1 (.pack cs x) m1 ->
  BigStep m1 (e2.subst (Subst.unpack cs x)) t2 v2 m2 ->
  BigStep m (.unpack e1 e2) (t1 ++ t2) v2 m2
| bs_read {m : Memory} {x n : Nat} :
  m.lookup x = some (.capability (.mcell n)) ->
  BigStep m (.read (.free x)) [.read x] (.var (.free n)) m
| bs_write {m : Memory} {x y : Nat} {n0 : Nat} :
  (hx : m.lookup x = some (.capability (.mcell n0))) ->
  (hy : m.heap y ≠ none) ->
  BigStep m (.write (.free x) (.free y)) [.access x] .unit (m.update_mcell x y ⟨n0, hx⟩ hy)
| bs_alloc {m : Memory} {x l : Nat} :
  (hx : m.heap x ≠ none) ->
  (hfresh : m.heap l = none) ->
  BigStep m (.alloc (.free x)) [.alloc l]
    (.pack (.var (.free l)) (.free l)) (m.extend_mcell l x hfresh hx)
| bs_cond_true {m : Memory} {x : Var .var {}} :
  resolve m.heap (.var x) = some .btrue ->
  BigStep m e2 t v m' ->
  BigStep m (.cond x e2 e3) t v m'
| bs_cond_false {m : Memory} {x : Var .var {}} :
  resolve m.heap (.var x) = some .bfalse ->
  BigStep m e3 t v m' ->
  BigStep m (.cond x e2 e3) t v m'

/-- **Budget- and authority-indexed safety.**  `Safe k R m e` means evaluating `e` from
  `m` never gets stuck along any partial run performing fewer than `k` reads, and every
  capability event of such a run is on a location in the authority `R` or allocated by the
  run itself.  The bottom `Safe 0 R m e` holds trivially: with no reads observable, nothing
  is claimed (the ▷-style bottom of the step-indexed model, placed in the operational
  safety predicate).  Continuations of `letin`/`unpack` run at the residual budget
  `k - t1.readCount` and may additionally use the cells the head allocated. -/
inductive Safe : Nat -> CapabilitySet -> Memory -> Exp {} -> Prop where
| exhausted {R : CapabilitySet} {m : Memory} {e : Exp {}} :
  Safe 0 R m e
| ans {k : Nat} {R : CapabilitySet} {m : Memory} {e : Exp {}} :
  e.IsAns -> Safe k R m e
| alloc {k : Nat} {R : CapabilitySet} {m : Memory} {x : Nat} :
  m.heap x ≠ none ->
  Safe k R m (.alloc (.free x))
| apply {k : Nat} {R : CapabilitySet} {m : Memory} {x y : Nat} :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R0⟩) ->
  Safe k R m (e.subst (Subst.openVar (.free y))) ->
  Safe k R m (.app (.free x) (.free y))
| invoke {k : Nat} {R : CapabilitySet} {m : Memory} {x y : Nat} :
  x ∈ R ->
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R0⟩) ->
  Safe k R m (.app (.free x) (.free y))
| tapply {k : Nat} {R : CapabilitySet} {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.tabs cs T0 e, hv, R0⟩) ->
  Safe k R m (e.subst (Subst.openTVar .top)) ->
  Safe k R m (.tapp (.free x) S)
| capply {k : Nat} {R : CapabilitySet} {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.cabs cs B0 e, hv, R0⟩) ->
  Safe k R m (e.subst (Subst.openCVar CS)) ->
  Safe k R m (.capp (.free x) CS)
| letin {k : Nat} {R : CapabilitySet} {m : Memory} :
  Safe k R m e1 ->
  -- answer-shape of the head is guaranteed only for runs WITHIN budget
  (h_ans : ∀ t1 v m1, BigStep m e1 t1 v m1 -> t1.readCount < k ->
    v.IsSimpleAns ∧ Exp.WfInHeap v m1.heap) ->
  (h_val : ∀ {t1 : Trace} {m1} {v : Exp {}},
    BigStep m e1 t1 v m1 -> (hv : Exp.IsSimpleVal v) -> (hwf_v : Exp.WfInHeap v m1.heap) ->
    ∀ l' (hfresh : m1.lookup l' = none),
      Safe (k - t1.readCount) (R ∪ CapabilitySet.ofList t1.allocList)
        (m1.extend_val l' ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh)
        (e2.subst (Subst.openVar (.free l')))) ->
  (h_var : ∀ {t1 : Trace} {m1} {x : Var .var {}},
    BigStep m e1 t1 (.var x) m1 ->
    Safe (k - t1.readCount) (R ∪ CapabilitySet.ofList t1.allocList) m1
      (e2.subst (Subst.openVar x))) ->
  Safe k R m (.letin e1 e2)
| unpack {k : Nat} {R : CapabilitySet} {m : Memory} {e1 : Exp {}} {e2 : Exp ({},C,x)} :
  Safe k R m e1 ->
  (h_ans : ∀ t1 v m1, BigStep m e1 t1 v m1 -> t1.readCount < k ->
    v.IsPack ∧ Exp.WfInHeap v m1.heap) ->
  (h_val : ∀ {t1 : Trace} {m1} {x : Var .var {}} {cs : CaptureSet {}},
    BigStep m e1 t1 (.pack cs x) m1 ->
    Safe (k - t1.readCount) (R ∪ CapabilitySet.ofList t1.allocList) m1
      (e2.subst (Subst.unpack cs x))) ->
  Safe k R m (.unpack e1 e2)
| read {k : Nat} {R : CapabilitySet} {m : Memory} {x n : Nat} :
  x ∈ R ->
  m.lookup x = some (.capability (.mcell n)) ->
  Safe k R m (.read (.free x))
| write {k : Nat} {R : CapabilitySet} {m : Memory} {x y : Nat} {n0 : Nat} :
  x ∈ R ->
  m.lookup x = some (.capability (.mcell n0)) ->
  m.heap y ≠ none ->
  Safe k R m (.write (.free x) (.free y))
| cond {k : Nat} {R : CapabilitySet} {m : Memory} {x : Var .var {}} :
  (resolve m.heap (.var x) = some .btrue ∨ resolve m.heap (.var x) = some .bfalse) ->
  (resolve m.heap (.var x) = some .btrue -> Safe k R m e2) ->
  (resolve m.heap (.var x) = some .bfalse -> Safe k R m e3) ->
  Safe k R m (.cond x e2 e3)

/-- Trace-observing evaluation predicate at read budget `k` and authority `R`: `e` from
  `m` is safe for `k` reads within authority `R`, and every answer it reaches satisfies
  `Q`.  The postcondition half quantifies over ALL runs, unconditionally — budget
  awareness lives in `Safe` and in the budget-guarded postconditions the denotations
  instantiate `Q` with. -/
def Eval (k : Nat) (R : CapabilitySet) (m : Memory) (e : Exp {}) (Q : Tpost) : Prop :=
  Safe k R m e ∧ (∀ t v m', BigStep m e t v m' -> Q t v m')

/-! ## Basic properties of `BigStep` -/

theorem Memory.lookup_val_eq {m : Memory} {x : Nat} {v1 v2 : HeapVal}
    (h1 : m.lookup x = some (.val v1)) (h2 : m.lookup x = some (.val v2)) : v1 = v2 :=
  Cell.val.inj (Option.some.inj (h1 ▸ h2))

/-- Every `BigStep` answer is an answer. -/
theorem BigStep.isAns {m e t v m'} (h : BigStep m e t v m') : v.IsAns := by
  induction h with
  | bs_pack => exact Exp.IsAns.is_val Exp.IsVal.pack
  | bs_val hv => exact Exp.IsAns.is_val (Exp.IsVal.of_simple hv)
  | bs_var => exact Exp.IsAns.is_var
  | bs_apply _ _ ih => exact ih
  | bs_invoke _ _ => exact Exp.IsAns.is_val Exp.IsVal.unit
  | bs_tapply _ _ ih => exact ih
  | bs_capply _ _ ih => exact ih
  | bs_letin_val _ _ _ _ _ _ ih => exact ih
  | bs_letin_var _ _ _ ih => exact ih
  | bs_unpack _ _ _ ih => exact ih
  | bs_read _ => exact Exp.IsAns.is_var
  | bs_write _ _ => exact Exp.IsAns.is_val Exp.IsVal.unit
  | bs_alloc _ _ => exact Exp.IsAns.is_val Exp.IsVal.pack
  | bs_cond_true _ _ ih => exact ih
  | bs_cond_false _ _ ih => exact ih

/-- `BigStep` evolves memory monotonically. -/
theorem BigStep.subsumes {m e t v m'} (h : BigStep m e t v m') : m'.subsumes m := by
  induction h with
  | bs_pack => exact Memory.subsumes_refl _
  | bs_val _ => exact Memory.subsumes_refl _
  | bs_var => exact Memory.subsumes_refl _
  | bs_apply _ _ ih => exact ih
  | bs_invoke _ _ => exact Memory.subsumes_refl _
  | bs_tapply _ _ ih => exact ih
  | bs_capply _ _ ih => exact ih
  | bs_letin_val _ _ hwf hfresh _ ih1 ih2 =>
    exact Memory.subsumes_trans ih2
      (Memory.subsumes_trans (Memory.extend_val_subsumes _ _ _ hwf rfl hfresh) ih1)
  | bs_letin_var _ _ ih1 ih2 => exact Memory.subsumes_trans ih2 ih1
  | bs_unpack _ _ ih1 ih2 => exact Memory.subsumes_trans ih2 ih1
  | bs_read _ => exact Memory.subsumes_refl _
  | bs_write hx hy => exact Memory.update_mcell_subsumes _ _ _ ⟨_, hx⟩ hy
  | bs_alloc hx hfresh => exact Memory.extend_mcell_subsumes _ _ _ hfresh hx
  | bs_cond_true _ _ ih => exact ih
  | bs_cond_false _ _ ih => exact ih

/-- An answer runs to itself with the empty trace. -/
theorem BigStep.of_isAns {m : Memory} {e : Exp {}} (h : e.IsAns) : BigStep m e [] e m := by
  cases h with
  | is_var => exact BigStep.bs_var
  | is_val hv =>
    cases hv with
    | pack => exact BigStep.bs_pack
    | abs => exact BigStep.bs_val Exp.IsSimpleVal.abs
    | tabs => exact BigStep.bs_val Exp.IsSimpleVal.tabs
    | cabs => exact BigStep.bs_val Exp.IsSimpleVal.cabs
    | unit => exact BigStep.bs_val Exp.IsSimpleVal.unit
    | btrue => exact BigStep.bs_val Exp.IsSimpleVal.btrue
    | bfalse => exact BigStep.bs_val Exp.IsSimpleVal.bfalse

/-- A simple value only runs to itself. -/
theorem BigStep.simpleVal_eq {m : Memory} {v : Exp {}} {t v' m'}
    (hv : Exp.IsSimpleVal v) (hbs : BigStep m v t v' m') : t = [] ∧ v' = v ∧ m' = m := by
  cases hv <;> cases hbs <;> exact ⟨rfl, rfl, rfl⟩

/-- An answer only runs to itself. -/
theorem BigStep.isAns_inv {m : Memory} {e : Exp {}} {t v m'}
    (hbs : BigStep m e t v m') (hans : e.IsAns) : t = [] ∧ v = e ∧ m' = m := by
  cases hans with
  | is_var =>
    cases hbs with
    | bs_var => exact ⟨rfl, rfl, rfl⟩
    | bs_val hv => cases hv
  | is_val hv =>
    cases hv with
    | pack => cases hbs with | bs_pack => exact ⟨rfl, rfl, rfl⟩ | bs_val hv => cases hv
    | abs => exact BigStep.simpleVal_eq Exp.IsSimpleVal.abs hbs
    | tabs => exact BigStep.simpleVal_eq Exp.IsSimpleVal.tabs hbs
    | cabs => exact BigStep.simpleVal_eq Exp.IsSimpleVal.cabs hbs
    | unit => exact BigStep.simpleVal_eq Exp.IsSimpleVal.unit hbs
    | btrue => exact BigStep.simpleVal_eq Exp.IsSimpleVal.btrue hbs
    | bfalse => exact BigStep.simpleVal_eq Exp.IsSimpleVal.bfalse hbs

/-! ## Basic properties of `Safe` and `Eval` -/

theorem CapabilitySet.union_mono_left {C1 C2 C : CapabilitySet} (h : C1 ⊆ C2) :
    C1 ∪ C ⊆ C2 ∪ C :=
  CapabilitySet.Subset.union_left
    (CapabilitySet.Subset.trans h CapabilitySet.Subset.union_right_left)
    CapabilitySet.Subset.union_right_right

/-- Safety is monotone in the authority. -/
theorem Safe.mono_auth {k : Nat} {R R' : CapabilitySet} {m : Memory} {e : Exp {}}
    (hsub : R ⊆ R') (h : Safe k R m e) : Safe k R' m e := by
  induction h generalizing R' with
  | exhausted => exact .exhausted
  | ans hans => exact .ans hans
  | alloc hx => exact .alloc hx
  | apply hlk _ ih => exact .apply hlk (ih hsub)
  | invoke hmem hx hy => exact .invoke (CapabilitySet.subset_preserves_mem hsub hmem) hx hy
  | tapply hlk _ ih => exact .tapply hlk (ih hsub)
  | capply hlk _ ih => exact .capply hlk (ih hsub)
  | letin _ h_ans _ _ ih ih_val ih_var =>
    refine .letin (ih hsub) h_ans ?_ ?_
    · intro t1 m1 v hbs hv hwf l' hfresh
      exact ih_val hbs hv hwf l' hfresh (CapabilitySet.union_mono_left hsub)
    · intro t1 m1 x hbs
      exact ih_var hbs (CapabilitySet.union_mono_left hsub)
  | unpack _ h_ans _ ih ih_val =>
    refine .unpack (ih hsub) h_ans ?_
    intro t1 m1 x cs hbs
    exact ih_val hbs (CapabilitySet.union_mono_left hsub)
  | read hmem hlk => exact .read (CapabilitySet.subset_preserves_mem hsub hmem) hlk
  | write hmem hx hy => exact .write (CapabilitySet.subset_preserves_mem hsub hmem) hx hy
  | cond hres _ _ ih2 ih3 =>
    exact .cond hres (fun h => ih2 h hsub) (fun h => ih3 h hsub)

/-- Safety is antitone in the budget. -/
theorem Safe.mono_budget {k j : Nat} {R : CapabilitySet} {m : Memory} {e : Exp {}}
    (hle : j ≤ k) (h : Safe k R m e) : Safe j R m e := by
  induction h generalizing j with
  | exhausted => rw [Nat.le_zero.mp hle]; exact .exhausted
  | ans hans => exact .ans hans
  | alloc hx => exact .alloc hx
  | apply hlk _ ih => exact .apply hlk (ih hle)
  | invoke hmem hx hy => exact .invoke hmem hx hy
  | tapply hlk _ ih => exact .tapply hlk (ih hle)
  | capply hlk _ ih => exact .capply hlk (ih hle)
  | letin _ h_ans _ _ ih ih_val ih_var =>
    refine .letin (ih hle) (fun t1 v m1 hbs hbud => h_ans t1 v m1 hbs (by omega)) ?_ ?_
    · intro t1 m1 v hbs hv hwf l' hfresh
      exact ih_val hbs hv hwf l' hfresh (Nat.sub_le_sub_right hle _)
    · intro t1 m1 x hbs
      exact ih_var hbs (Nat.sub_le_sub_right hle _)
  | unpack _ h_ans _ ih ih_val =>
    refine .unpack (ih hle) (fun t1 v m1 hbs hbud => h_ans t1 v m1 hbs (by omega)) ?_
    intro t1 m1 x cs hbs
    exact ih_val hbs (Nat.sub_le_sub_right hle _)
  | read hmem hlk => exact .read hmem hlk
  | write hmem hx hy => exact .write hmem hx hy
  | cond hres _ _ ih2 ih3 =>
    exact .cond hres (fun h => ih2 h hle) (fun h => ih3 h hle)

theorem Eval.mono_auth {k : Nat} {R R' : CapabilitySet} {m : Memory} {e : Exp {}} {Q : Tpost}
    (hsub : R ⊆ R') (h : Eval k R m e Q) : Eval k R' m e Q :=
  ⟨Safe.mono_auth hsub h.1, h.2⟩

/-- Postconditions of `Eval` may be weakened. -/
theorem eval_post_monotonic {k : Nat} {R : CapabilitySet} {m : Memory} {e : Exp {}}
    {Q1 Q2 : Tpost}
    (himp : ∀ t v m', BigStep m e t v m' -> Q1 t v m' -> Q2 t v m')
    (heval : Eval k R m e Q1) : Eval k R m e Q2 :=
  ⟨heval.1, fun t v m' hbs => himp t v m' hbs (heval.2 t v m' hbs)⟩

theorem eval_post_entails {k : Nat} {R : CapabilitySet} {m : Memory} {e : Exp {}}
    {Q1 Q2 : Tpost}
    (himp : Q1.entails Q2) (heval : Eval k R m e Q1) : Eval k R m e Q2 :=
  eval_post_monotonic (fun t v m' _ h => himp t v m' h) heval

/-- At read budget `0`, ANY expression satisfies `Eval` with a budget-guarded
  postcondition: safety is `Safe.exhausted` and the guard `t.readCount < 0` is vacuous. -/
theorem Eval.exhausted {R : CapabilitySet} {m : Memory} {e : Exp {}}
    {P : Trace -> Exp {} -> Memory -> Prop} :
    Eval 0 R m e (fun t v m' => t.readCount < 0 -> P t v m') :=
  ⟨Safe.exhausted, fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- If an answer has an evaluation, then the postcondition holds for it with the
  empty trace. -/
theorem eval_ans_holds_post {k : Nat} {R : CapabilitySet} {m : Memory} {e : Exp {}} {Q : Tpost}
    (heval : Eval k R m e Q) (hans : e.IsAns) : Q [] e m :=
  heval.2 _ _ _ (BigStep.of_isAns hans)

/-! ## Introduction lemmas for `Eval` -/

theorem Eval.eval_pack {k : Nat} {R : CapabilitySet} {m : Memory} {cs : CaptureSet {}}
    {x : Var .var {}} {Q : Tpost}
    (hQ : Q [] (.pack cs x) m) : Eval k R m (.pack cs x) Q := by
  refine ⟨Safe.ans (Exp.IsAns.is_val Exp.IsVal.pack), ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_pack => exact hQ
  | bs_val hv => cases hv

theorem Eval.eval_var {k : Nat} {R : CapabilitySet} {m : Memory} {x : Var .var {}} {Q : Tpost}
    (hQ : Q [] (.var x) m) : Eval k R m (.var x) Q := by
  refine ⟨Safe.ans Exp.IsAns.is_var, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_var => exact hQ
  | bs_val hv => cases hv

theorem Eval.eval_val {k : Nat} {R : CapabilitySet} {m : Memory} {v : Exp {}} {Q : Tpost}
    (hv : Exp.IsSimpleVal v) (hQ : Q [] v m) : Eval k R m v Q := by
  refine ⟨Safe.ans (Exp.IsAns.is_val (Exp.IsVal.of_simple hv)), ?_⟩
  intro t v' m' hbs
  obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq hv hbs
  exact hQ

theorem Eval.eval_apply {k : Nat} {R : CapabilitySet} {m : Memory} {x y : Nat}
    {cs T e hv R0} {Q : Tpost}
    (hlk : m.lookup x = some (.val ⟨.abs cs T e, hv, R0⟩))
    (hrec : Eval k R m (e.subst (Subst.openVar (.free y))) Q) :
    Eval k R m (.app (.free x) (.free y)) Q := by
  refine ⟨Safe.apply hlk hrec.1, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_apply hlk2 hbody =>
    have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
    simp only at heq; cases heq
    exact hrec.2 _ _ _ hbody
  | bs_invoke hlkx2 _ => rw [hlk] at hlkx2; exact absurd hlkx2 (by simp)
  | bs_val hv => cases hv

theorem Eval.eval_invoke {k : Nat} {R : CapabilitySet} {m : Memory} {x y : Nat} {hv R0}
    {Q : Tpost}
    (hmem : x ∈ R)
    (hlkx : m.lookup x = some (.capability .basic))
    (hlky : m.lookup y = some (.val ⟨.unit, hv, R0⟩))
    (hQ : Q [.access x] .unit m) :
    Eval k R m (.app (.free x) (.free y)) Q := by
  refine ⟨Safe.invoke hmem hlkx hlky, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_apply hlk2 _ => rw [hlkx] at hlk2; exact absurd hlk2 (by simp)
  | bs_invoke _ _ => exact hQ
  | bs_val hv => cases hv

theorem Eval.eval_tapply {k : Nat} {R : CapabilitySet} {m : Memory} {x : Nat} {S}
    {cs T0 e hv R0} {Q : Tpost}
    (hlk : m.lookup x = some (.val ⟨.tabs cs T0 e, hv, R0⟩))
    (hrec : Eval k R m (e.subst (Subst.openTVar .top)) Q) :
    Eval k R m (.tapp (.free x) S) Q := by
  refine ⟨Safe.tapply hlk hrec.1, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_tapply hlk2 hbody =>
    have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
    simp only at heq; cases heq
    exact hrec.2 _ _ _ hbody
  | bs_val hv => cases hv

theorem Eval.eval_capply {k : Nat} {R : CapabilitySet} {m : Memory} {x : Nat} {CS}
    {cs B0 e hv R0} {Q : Tpost}
    (hlk : m.lookup x = some (.val ⟨.cabs cs B0 e, hv, R0⟩))
    (hrec : Eval k R m (e.subst (Subst.openCVar CS)) Q) :
    Eval k R m (.capp (.free x) CS) Q := by
  refine ⟨Safe.capply hlk hrec.1, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_capply hlk2 hbody =>
    have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
    simp only at heq; cases heq
    exact hrec.2 _ _ _ hbody
  | bs_val hv => cases hv

theorem Eval.eval_read {k : Nat} {R : CapabilitySet} {m : Memory} {x n : Nat} {Q : Tpost}
    (hmem : x ∈ R)
    (hlk : m.lookup x = some (.capability (.mcell n)))
    (hQ : Q [.read x] (.var (.free n)) m) :
    Eval k R m (.read (.free x)) Q := by
  refine ⟨Safe.read hmem hlk, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_read hlk2 =>
    cases hlk.symm.trans hlk2
    exact hQ
  | bs_val hv => cases hv

theorem Eval.eval_write {k : Nat} {R : CapabilitySet} {m : Memory} {x y : Nat} {n0 : Nat}
    {Q : Tpost}
    (hmem : x ∈ R)
    (hx : m.lookup x = some (.capability (.mcell n0)))
    (hy : m.heap y ≠ none)
    (hQ : Q [.access x] .unit (m.update_mcell x y ⟨n0, hx⟩ hy)) :
    Eval k R m (.write (.free x) (.free y)) Q := by
  refine ⟨Safe.write hmem hx hy, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_write hx2 hy2 => exact hQ
  | bs_val hv => cases hv

theorem Eval.eval_alloc {k : Nat} {R : CapabilitySet} {m : Memory} {x : Nat} {Q : Tpost}
    (hx : m.heap x ≠ none)
    (h_post : ∀ l (hfresh : m.heap l = none),
      Q [.alloc l] (.pack (.var (.free l)) (.free l)) (m.extend_mcell l x hfresh hx)) :
    Eval k R m (.alloc (.free x)) Q := by
  refine ⟨Safe.alloc hx, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_alloc hx2 hfresh2 => exact h_post _ hfresh2
  | bs_val hv => cases hv

theorem Eval.eval_cond {k : Nat} {R : CapabilitySet} {m : Memory} {x : Var .var {}}
    {e2 e3 : Exp {}} {Q : Tpost}
    (hres : resolve m.heap (.var x) = some .btrue ∨ resolve m.heap (.var x) = some .bfalse)
    (h_true : resolve m.heap (.var x) = some .btrue -> Eval k R m e2 Q)
    (h_false : resolve m.heap (.var x) = some .bfalse -> Eval k R m e3 Q) :
    Eval k R m (.cond x e2 e3) Q := by
  refine ⟨Safe.cond hres (fun ht => (h_true ht).1) (fun hf => (h_false hf).1), ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_cond_true hres_t hbody => exact (h_true hres_t).2 _ _ _ hbody
  | bs_cond_false hres_f hbody => exact (h_false hres_f).2 _ _ _ hbody
  | bs_val hv => cases hv

/-- `letin`: run the head, then the continuation at the residual budget and with
  authority extended by the head's allocations.  Continuation obligations are only owed
  for within-budget head runs; overflow runs are internalized by `hQ_over`. -/
theorem Eval.eval_letin {k : Nat} {R : CapabilitySet} {m : Memory} {e1 : Exp {}}
    {e2 : Exp ({},x)} {Q Q1 : Tpost}
    (he1 : Eval k R m e1 Q1)
    (hQ_over : ∀ t v m', k ≤ t.readCount -> Q t v m')
    (h_nonstuck : ∀ {t1 : Trace} {m1 : Memory} {v : Exp {}}, t1.readCount < k ->
      Q1 t1 v m1 -> v.IsSimpleAns ∧ Exp.WfInHeap v m1.heap)
    (h_val : ∀ {t1 : Trace} {m1} {v : Exp {}}, t1.readCount < k ->
      m1.subsumes m ->
      (hv : Exp.IsSimpleVal v) -> (hwf_v : Exp.WfInHeap v m1.heap) -> Q1 t1 v m1 ->
      ∀ l' (hfresh : m1.lookup l' = none),
        Eval (k - t1.readCount) (R ∪ CapabilitySet.ofList t1.allocList)
          (m1.extend_val l' ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh)
          (e2.subst (Subst.openVar (.free l'))) (fun t2 => Q (t1 ++ t2)))
    (h_var : ∀ {t1 : Trace} {m1} {x : Var .var {}}, t1.readCount < k ->
      m1.subsumes m ->
      (hwf_x : x.WfInHeap m1.heap) -> Q1 t1 (.var x) m1 ->
      Eval (k - t1.readCount) (R ∪ CapabilitySet.ofList t1.allocList) m1
        (e2.subst (Subst.openVar x)) (fun t2 => Q (t1 ++ t2))) :
    Eval k R m (.letin e1 e2) Q := by
  refine ⟨?_, ?_⟩
  · refine Safe.letin he1.1
      (fun t1 v m1 hrun hbud => h_nonstuck hbud (he1.2 t1 v m1 hrun)) ?_ ?_
    · intro t1 m1 v hrun hv hwf_v l' hfresh
      rcases Nat.lt_or_ge t1.readCount k with hbud | hover
      · exact (h_val hbud (BigStep.subsumes hrun) hv hwf_v (he1.2 t1 v m1 hrun) l' hfresh).1
      · rw [Nat.sub_eq_zero_of_le hover]; exact Safe.exhausted
    · intro t1 m1 x hrun
      rcases Nat.lt_or_ge t1.readCount k with hbud | hover
      · have hq1 := he1.2 t1 (.var x) m1 hrun
        have hwfx : x.WfInHeap m1.heap := by
          cases (h_nonstuck hbud hq1).2 with | wf_var h => exact h
        exact (h_var hbud (BigStep.subsumes hrun) hwfx hq1).1
      · rw [Nat.sub_eq_zero_of_le hover]; exact Safe.exhausted
  · intro t v m' hbs
    cases hbs with
    | bs_letin_val hrun_e1 hv hwf_v hfresh hrun_e2 =>
      rename_i t1 t2 _ _ _
      rcases Nat.lt_or_ge t1.readCount k with hbud | hover
      · exact (h_val hbud (BigStep.subsumes hrun_e1) hv hwf_v
          (he1.2 _ _ _ hrun_e1) _ hfresh).2 _ _ _ hrun_e2
      · exact hQ_over _ _ _ (by rw [Trace.readCount_append]; omega)
    | bs_letin_var hrun_e1 hrun_e2 =>
      rename_i t1 t2 _ _
      rcases Nat.lt_or_ge t1.readCount k with hbud | hover
      · have hq1 := he1.2 _ _ _ hrun_e1
        cases (h_nonstuck hbud hq1).2 with
        | wf_var hwfx =>
          exact (h_var hbud (BigStep.subsumes hrun_e1) hwfx hq1).2 _ _ _ hrun_e2
      · exact hQ_over _ _ _ (by rw [Trace.readCount_append]; omega)
    | bs_val hv => cases hv

/-- `unpack`: like `letin`, but the head answer is a `pack`. -/
theorem Eval.eval_unpack {k : Nat} {R : CapabilitySet} {m : Memory} {e1 : Exp {}}
    {e2 : Exp ({},C,x)} {Q Q1 : Tpost}
    (he1 : Eval k R m e1 Q1)
    (hQ_over : ∀ t v m', k ≤ t.readCount -> Q t v m')
    (h_nonstuck : ∀ {t1 : Trace} {m1 : Memory} {v : Exp {}}, t1.readCount < k ->
      Q1 t1 v m1 -> v.IsPack ∧ Exp.WfInHeap v m1.heap)
    (h_val : ∀ {t1 : Trace} {m1} {x : Var .var {}} {cs : CaptureSet {}},
      t1.readCount < k ->
      m1.subsumes m ->
      (hwf_x : x.WfInHeap m1.heap) ->
      (hwf_cs : cs.WfInHeap m1.heap) ->
      Q1 t1 (.pack cs x) m1 ->
      Eval (k - t1.readCount) (R ∪ CapabilitySet.ofList t1.allocList) m1
        (e2.subst (Subst.unpack cs x)) (fun t2 => Q (t1 ++ t2))) :
    Eval k R m (.unpack e1 e2) Q := by
  refine ⟨?_, ?_⟩
  · refine Safe.unpack he1.1
      (fun t1 v m1 hrun hbud => h_nonstuck hbud (he1.2 t1 v m1 hrun)) ?_
    intro t1 m1 x cs hrun
    rcases Nat.lt_or_ge t1.readCount k with hbud | hover
    · have hq1 := he1.2 t1 (.pack cs x) m1 hrun
      cases (h_nonstuck hbud hq1).2 with
      | wf_pack hcs hx =>
        exact (h_val hbud (BigStep.subsumes hrun) hx hcs hq1).1
    · rw [Nat.sub_eq_zero_of_le hover]; exact Safe.exhausted
  · intro t v m' hbs
    cases hbs with
    | bs_unpack hrun_e1 hrun_e2 =>
      rename_i t1 t2 _ _ _
      rcases Nat.lt_or_ge t1.readCount k with hbud | hover
      · have hq1 := he1.2 _ _ _ hrun_e1
        cases (h_nonstuck hbud hq1).2 with
        | wf_pack hcs hx =>
          exact (h_val hbud (BigStep.subsumes hrun_e1) hx hcs hq1).2 _ _ _ hrun_e2
      · exact hQ_over _ _ _ (by rw [Trace.readCount_append]; omega)
    | bs_val hv => cases hv

end CC
