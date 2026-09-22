import Semantic.CC.Syntax
import Semantic.CC.Substitution
import Semantic.CC.Semantics.Heap
import Semantic.CC.Semantics.Trace

namespace CC

/-- Small-step evaluation relation instrumented with a trace.
  `Step t m e m' e'` means that expression `e` in memory `m` steps to `e'` in memory `m'`,
  emitting the trace `t` of heap events performed by this step. -/
inductive Step : Trace -> Memory -> Exp {} -> Memory -> Exp {} -> Prop where
| step_apply :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  Step [] m (.app (.free x) (.free y)) m (e.subst (Subst.openVar (.free y)))
| step_invoke :
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  Step [.access x] m (.app (.free x) (.free y)) m .unit
| step_tapply :
  m.lookup x = some (.val ⟨.tabs cs S' e, hv, R⟩) ->
  Step [] m (.tapp (.free x) S) m (e.subst (Subst.openTVar .top))
| step_capply :
  m.lookup x = some (.val ⟨.cabs cs B e, hv, R⟩) ->
  Step [] m (.capp (.free x) CS) m (e.subst (Subst.openCVar CS))
| step_cond_var_true :
  m.lookup x = some (.val ⟨.btrue, hv, R⟩) ->
  Step [] m (.cond (.free x) e1 e2) m e1
| step_cond_var_false :
  m.lookup x = some (.val ⟨.bfalse, hv, R⟩) ->
  Step [] m (.cond (.free x) e1 e2) m e2
-- `read` dereferences the cell: it returns a reference to the stored location `n`.
| step_read :
  m.lookup x = some (.capability (.mcell n)) ->
  Step [.read x] m (.read (.free x)) m (.var (.free n))
-- `write` stores the location `y` of the (present) new content.
| step_write :
  (hx : m.lookup x = some (.capability (.mcell n0))) ->
  (hy : m.heap y ≠ none) ->
  Step [.access x] m (.write (.free x) (.free y)) (m.update_mcell x y ⟨n0, hx⟩ hy) .unit
-- `alloc` creates a fresh cell storing `x`, and returns it packed with its own
-- capture set as evidence.
| step_alloc :
  (hx : m.heap x ≠ none) ->
  (hfresh : m.heap l = none) ->
  Step [.alloc l] m (.alloc (.free x))
    (m.extend_mcell l x hfresh hx)
    (.pack (.var (.free l)) (.free l))
| step_ctx_letin :
  Step t m e1 m' e1' ->
  Step t m (.letin e1 e2) m' (.letin e1' e2)
| step_ctx_unpack :
  Step t m e1 m' e1' ->
  Step t m (.unpack e1 e2) m' (.unpack e1' e2)
| step_rename :
  Step [] m (.letin (.var (.free y)) e) m (e.subst (Subst.openVar (.free y)))
-- Lifting a value to the heap is not a capability event: it emits no trace.
| step_lift :
  (hv : Exp.IsSimpleVal v) ->
  (hwf : Exp.WfInHeap v m.heap) ->
  (hfresh : m.heap l = none) ->
  Step
    []
    m (.letin v e)
    (m.extend_val l ⟨v, hv, compute_reachability m.heap v hv⟩ hwf rfl hfresh)
    (e.subst (Subst.openVar (.free l)))
| step_unpack :
  Step [] m (.unpack (.pack cs (.free x)) e) m (e.subst (Subst.unpack cs (.free x)))

/-- Multi-step reduction: the reflexive-transitive closure of `Step`, accumulating the
  traces of the individual steps in order. -/
inductive Reduce : Trace -> Memory -> Exp {} -> Memory -> Exp {} -> Prop where
| refl :
  Reduce [] m e m e
| step :
  Step t1 m1 e1 m2 e2 ->
  Reduce t2 m2 e2 m3 e3 ->
  Reduce (t1 ++ t2) m1 e1 m3 e3

theorem reduce_trans
  (hred1 : Reduce t1 m1 e1 m2 e2)
  (hred2 : Reduce t2 m2 e2 m3 e3) :
  Reduce (t1 ++ t2) m1 e1 m3 e3 := by
  induction hred1 with
  | refl => exact hred2
  | step h rest ih =>
    rw [List.append_assoc]
    exact Reduce.step h (ih hred2)

theorem reduce_ctx_letin
  (hred : Reduce t m e1 m' e1') :
  Reduce t m (.letin e1 e2) m' (.letin e1' e2) := by
  induction hred with
  | refl => exact Reduce.refl
  | step hstep _ ih => exact Reduce.step (Step.step_ctx_letin hstep) ih

theorem reduce_ctx_unpack
  (hred : Reduce t m e1 m' e1') :
  Reduce t m (.unpack e1 e2) m' (.unpack e1' e2) := by
  induction hred with
  | refl => exact Reduce.refl
  | step hstep _ ih => exact Reduce.step (Step.step_ctx_unpack hstep) ih

/-- Answers (values and variables) take no step. -/
theorem step_ans_absurd
  (hans : Exp.IsAns e)
  (hstep : Step t m e m' e') :
  False := by
  cases hans with
  | is_val hv => cases hv <;> cases hstep
  | is_var => cases hstep

/-- A reduction from an answer is trivial. -/
theorem reduce_ans_eq
  (hans : Exp.IsAns e)
  (hred : Reduce t m e m' e') :
  m' = m ∧ e' = e ∧ t = [] := by
  cases hred with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | step hstep _ => exact (step_ans_absurd hans hstep).elim

theorem step_memory_monotonic
  (hstep : Step t m e m' e') :
  m'.subsumes m := by
  induction hstep with
  | step_apply _ => exact Memory.subsumes_refl _
  | step_invoke _ _ => exact Memory.subsumes_refl _
  | step_tapply _ => exact Memory.subsumes_refl _
  | step_capply _ => exact Memory.subsumes_refl _
  | step_cond_var_true _ => exact Memory.subsumes_refl _
  | step_cond_var_false _ => exact Memory.subsumes_refl _
  | step_read _ => exact Memory.subsumes_refl _
  | step_write hx hy => exact Memory.update_mcell_subsumes _ _ _ ⟨_, hx⟩ hy
  | step_alloc hx hfresh => exact Memory.extend_mcell_subsumes _ _ _ hfresh hx
  | step_ctx_letin _ ih => exact ih
  | step_ctx_unpack _ ih => exact ih
  | step_rename => exact Memory.subsumes_refl _
  | step_lift hv hwf hfresh => exact Memory.extend_val_subsumes _ _ _ hwf rfl hfresh
  | step_unpack => exact Memory.subsumes_refl _

theorem reduce_memory_monotonic
  (hred : Reduce t m e m' e') :
  m'.subsumes m := by
  induction hred with
  | refl => exact Memory.subsumes_refl _
  | step hstep _ ih => exact Memory.subsumes_trans ih (step_memory_monotonic hstep)

end CC
