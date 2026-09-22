import Semantic.CC.Semantics.SmallStep
import Semantic.CC.Semantics.BigStep

/-!
# Properties of the semantics

The bridge between the small-step relation `Step`/`Reduce` and the big-step relation
`BigStep` (head expansion), and the two adequacy-facing consequences of `Safe`: every
state reachable within budget is progressive (`safe_reduce_progressive`), and every
within-budget partial run is authorized (`safe_reduce_traceok`).
-/

namespace CC

/-- The result of looking up a variable in the heap is deterministic. -/
theorem Heap.lookup_deterministic {H : Heap}
  (hlookup1 : H l = some v1)
  (hlookup2 : H l = some v2) :
  v1 = v2 := by grind

/-- The result of looking up a variable in the memory is deterministic. -/
theorem Memory.lookup_deterministic {m : Memory}
  (hlookup1 : m.lookup l = some v1)
  (hlookup2 : m.lookup l = some v2) :
  v1 = v2 := by
  cases m
  simp only [Memory.lookup] at hlookup1 hlookup2
  apply Heap.lookup_deterministic hlookup1 hlookup2

/-- A variable in the empty signature is always free. -/
theorem Var.free_cases {k : Kind} (x : Var k {}) : ∃ n, x = .free n := by
  cases x with
  | bound b => cases b
  | free n => exact ⟨n, rfl⟩

/-- Resolving a variable to a value exhibits the heap value. -/
theorem resolve_var_inv {H : Heap} {x : Var .var {}} {e : Exp {}}
    (h : resolve H (.var x) = some e) :
    ∃ (fx : Nat) (hv : e.IsSimpleVal) (R : CapabilitySet),
      x = .free fx ∧ H fx = some (.val ⟨e, hv, R⟩) := by
  obtain ⟨fx, rfl⟩ := Var.free_cases x
  cases hcell : H fx with
  | none => simp [resolve, hcell] at h
  | some c =>
    cases c with
    | val v =>
      obtain ⟨u, hv, R⟩ := v
      simp only [resolve, hcell] at h
      injection h with h
      subst h
      exact ⟨fx, hv, R, rfl, hcell⟩
    | capability _ => simp [resolve, hcell] at h
    | masked => simp [resolve, hcell] at h

theorem resolve_of_lookup {H : Heap} {fx : Nat} {e : Exp {}} {hv : e.IsSimpleVal}
    {R : CapabilitySet} (h : H fx = some (.val ⟨e, hv, R⟩)) :
    resolve H (.var (.free fx)) = some e := by
  simp [resolve, h]

/-- A simple answer is a simple value or a free variable. -/
theorem Exp.isSimpleAns_cases {e : Exp {}} (h : e.IsSimpleAns) :
    e.IsSimpleVal ∨ ∃ n, e = .var (.free n) := by
  cases h with
  | is_simple_val hv => exact Or.inl hv
  | is_var =>
    rename_i x
    obtain ⟨n, rfl⟩ := Var.free_cases x
    exact Or.inr ⟨n, rfl⟩

theorem Exp.isPack_cases {e : Exp {}} (h : e.IsPack) :
    ∃ cs n, e = .pack cs (.free n) := by
  cases h with
  | pack =>
    rename_i cs x
    obtain ⟨n, rfl⟩ := Var.free_cases x
    exact ⟨cs, n, rfl⟩

/-! ## Progress -/

/-- A configuration is progressive when it is an answer or can take a step. -/
inductive IsProgressive : Memory -> Exp {} -> Prop where
| done :
  e.IsAns ->
  IsProgressive m e
| step :
  Step t m e m' e' ->
  IsProgressive m e

/-- Progress: a configuration safe for a positive budget is progressive. -/
theorem safe_implies_progressive {k : Nat} {R : CapabilitySet} {m : Memory} {e : Exp {}}
  (h : Safe k R m e) (hk : 0 < k) :
  IsProgressive m e := by
  revert hk
  induction h with
  | exhausted => intro hk; exact absurd hk (Nat.lt_irrefl 0)
  | ans hans => intro _; exact IsProgressive.done hans
  | alloc hlookup =>
    intro _
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact IsProgressive.step (Step.step_alloc (l := l) hlookup hfresh)
  | apply hlookup _ _ =>
    intro _
    exact IsProgressive.step (Step.step_apply hlookup)
  | invoke _ hlookup_x hlookup_y =>
    intro _
    exact IsProgressive.step (Step.step_invoke hlookup_x hlookup_y)
  | tapply hlookup _ _ =>
    intro _
    exact IsProgressive.step (Step.step_tapply hlookup)
  | capply hlookup _ _ =>
    intro _
    exact IsProgressive.step (Step.step_capply hlookup)
  | letin _ h_ans _ _ ih1 _ _ =>
    intro hk
    cases ih1 hk with
    | step hstep => exact IsProgressive.step (Step.step_ctx_letin hstep)
    | done hans =>
      obtain ⟨hsa, hwf⟩ := h_ans _ _ _ (BigStep.of_isAns hans) (by simpa using hk)
      rcases Exp.isSimpleAns_cases hsa with hv | ⟨n, rfl⟩
      · obtain ⟨l0, hfresh⟩ := Memory.exists_fresh _
        exact IsProgressive.step (Step.step_lift (l := l0) hv hwf hfresh)
      · exact IsProgressive.step Step.step_rename
  | unpack _ h_ans _ ih1 _ =>
    intro hk
    cases ih1 hk with
    | step hstep => exact IsProgressive.step (Step.step_ctx_unpack hstep)
    | done hans =>
      obtain ⟨hpk, _⟩ := h_ans _ _ _ (BigStep.of_isAns hans) (by simpa using hk)
      obtain ⟨cs, n, rfl⟩ := Exp.isPack_cases hpk
      exact IsProgressive.step Step.step_unpack
  | read _ hlookup =>
    intro _
    exact IsProgressive.step (Step.step_read hlookup)
  | write _ hx hy =>
    intro _
    exact IsProgressive.step (Step.step_write hx hy)
  | cond hres _ _ _ _ =>
    intro _
    rcases hres with hres | hres
    · obtain ⟨fx, hv, R0, rfl, hlk⟩ := resolve_var_inv hres
      exact IsProgressive.step (Step.step_cond_var_true (hv := hv) (R := R0) hlk)
    · obtain ⟨fx, hv, R0, rfl, hlk⟩ := resolve_var_inv hres
      exact IsProgressive.step (Step.step_cond_var_false (hv := hv) (R := R0) hlk)

theorem eval_implies_progressive {k : Nat} {R : CapabilitySet} {m : Memory} {e : Exp {}}
  {Q : Tpost}
  (heval : Eval k R m e Q) (hk : 0 < k) :
  IsProgressive m e :=
  safe_implies_progressive heval.1 hk

/-! ## Small-step ↔ big-step bridge -/

/-- **Head expansion**: prepending a `Step` to a `BigStep` run is again a `BigStep` run. -/
theorem BigStep.head_expand {t : Trace} {m1 e1 m2 e2 : _}
    (hstep : Step t m1 e1 m2 e2) :
    ∀ {t' : Trace} {v : Exp {}} {m' : Memory},
      BigStep m2 e2 t' v m' → BigStep m1 e1 (t ++ t') v m' := by
  induction hstep with
  | step_apply hlk => intro t' v m' hbs; exact BigStep.bs_apply hlk hbs
  | step_invoke hlkx hlky =>
    intro t' v m' hbs
    obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq Exp.IsSimpleVal.unit hbs
    exact BigStep.bs_invoke hlkx hlky
  | step_tapply hlk => intro t' v m' hbs; exact BigStep.bs_tapply hlk hbs
  | step_capply hlk => intro t' v m' hbs; exact BigStep.bs_capply hlk hbs
  | step_cond_var_true hlk =>
    intro t' v m' hbs
    exact BigStep.bs_cond_true (resolve_of_lookup hlk) hbs
  | step_cond_var_false hlk =>
    intro t' v m' hbs
    exact BigStep.bs_cond_false (resolve_of_lookup hlk) hbs
  | step_read hlk =>
    intro t' v m' hbs
    cases hbs with
    | bs_var => simpa using BigStep.bs_read hlk
    | bs_val hv => cases hv
  | step_write hx hy =>
    intro t' v m' hbs
    obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq Exp.IsSimpleVal.unit hbs
    exact BigStep.bs_write hx hy
  | step_alloc hx hfresh =>
    intro t' v m' hbs
    cases hbs with
    | bs_pack => exact BigStep.bs_alloc hx hfresh
    | bs_val hv => cases hv
  | step_ctx_letin _ ih =>
    intro t' v m' hbs
    cases hbs with
    | bs_letin_val hrun hv hwf hfresh hrun2 =>
      rw [← List.append_assoc]; exact BigStep.bs_letin_val (ih hrun) hv hwf hfresh hrun2
    | bs_letin_var hrun hrun2 =>
      rw [← List.append_assoc]; exact BigStep.bs_letin_var (ih hrun) hrun2
    | bs_val hv => cases hv
  | step_ctx_unpack _ ih =>
    intro t' v m' hbs
    cases hbs with
    | bs_unpack hrun hrun2 =>
      rw [← List.append_assoc]; exact BigStep.bs_unpack (ih hrun) hrun2
    | bs_val hv => cases hv
  | step_rename => intro t' v m' hbs; exact BigStep.bs_letin_var BigStep.bs_var hbs
  | step_lift hv hwf hfresh =>
    intro t' v' m' hbs
    exact BigStep.bs_letin_val (BigStep.bs_val hv) hv hwf hfresh hbs
  | step_unpack => intro t' v m' hbs; exact BigStep.bs_unpack BigStep.bs_pack hbs

/-- Small-step ⇒ big-step (to answers): a `Reduce` to an answer is realized by a single
  `BigStep` emitting the same trace. -/
theorem reduce_to_bigstep {t : Trace} {m e m' a}
    (hred : Reduce t m e m' a) (hans : a.IsAns) : BigStep m e t a m' := by
  induction hred with
  | refl => exact BigStep.of_isAns hans
  | step hstep _ ih => exact BigStep.head_expand hstep (ih hans)

/-- Any answer reachable from a configuration with an evaluation satisfies the
  postcondition. -/
theorem eval_to_reduce {k : Nat} {R : CapabilitySet} {t : Trace} {m e m' a} {Q : Tpost}
    (heval : Eval k R m e Q) (hred : Reduce t m e m' a) (hans : a.IsAns) :
    Q t a m' :=
  heval.2 _ _ _ (reduce_to_bigstep hred hans)

/-! ## Decomposition of reductions -/

/-- **Mid-run decomposition of a `letin` reduction.**  A `Reduce` from `.letin e1 e2`
  either (i) stays inside the head, or crosses into the opened continuation after the
  head reached (ii) a variable (`step_rename`) or (iii) a simple value (`step_lift`). -/
theorem reduce_letin_split {t : Trace} {m m' : Memory} {e1 : Exp {}}
    {e2 : Exp ({},x)} {X : Exp {}}
    (hred : Reduce t m (.letin e1 e2) m' X) :
    (∃ e1', Reduce t m e1 m' e1' ∧ X = .letin e1' e2) ∨
    (∃ (t1 t2 : Trace) (m1 : Memory) (y : Nat),
      Reduce t1 m e1 m1 (.var (.free y)) ∧
      Reduce t2 m1 (e2.subst (Subst.openVar (.free y))) m' X ∧ t = t1 ++ t2) ∨
    (∃ (t1 t2 : Trace) (m1 : Memory) (v : Exp {}) (hv : v.IsSimpleVal)
       (hwf : Exp.WfInHeap v m1.heap) (l : Nat) (hfresh : m1.heap l = none),
      Reduce t1 m e1 m1 v ∧
      Reduce t2
        (m1.extend_val l ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf rfl hfresh)
        (e2.subst (Subst.openVar (.free l))) m' X ∧ t = t1 ++ t2) := by
  generalize hgen : Exp.letin e1 e2 = efull at hred
  induction hred generalizing e1 with
  | refl => exact Or.inl ⟨e1, Reduce.refl, hgen.symm⟩
  | step hstep rest ih =>
    rw [←hgen] at hstep
    cases hstep with
    | step_ctx_letin hstep1 =>
      rcases ih rfl with ⟨e1', hr, hX⟩ | ⟨t1, t2, m1, y, hr1, hr2, ht⟩ |
        ⟨t1, t2, m1, v, hv, hwf, l, hfresh, hr1, hr2, ht⟩
      · exact Or.inl ⟨e1', Reduce.step hstep1 hr, hX⟩
      · exact Or.inr (Or.inl ⟨_, t2, m1, y, Reduce.step hstep1 hr1, hr2,
          by rw [ht, List.append_assoc]⟩)
      · exact Or.inr (Or.inr ⟨_, t2, m1, v, hv, hwf, l, hfresh,
          Reduce.step hstep1 hr1, hr2, by rw [ht, List.append_assoc]⟩)
    | step_rename =>
      exact Or.inr (Or.inl ⟨[], _, _, _, Reduce.refl, rest, rfl⟩)
    | step_lift hv hwf hfresh =>
      exact Or.inr (Or.inr ⟨[], _, _, _, hv, hwf, _, hfresh, Reduce.refl, rest, rfl⟩)

/-- `unpack` analogue of `reduce_letin_split`. -/
theorem reduce_unpack_split {t : Trace} {m m' : Memory} {e1 : Exp {}}
    {e2 : Exp ({},C,x)} {X : Exp {}}
    (hred : Reduce t m (.unpack e1 e2) m' X) :
    (∃ e1', Reduce t m e1 m' e1' ∧ X = .unpack e1' e2) ∨
    (∃ (t1 t2 : Trace) (m1 : Memory) (cs : CaptureSet {}) (y : Nat),
      Reduce t1 m e1 m1 (.pack cs (.free y)) ∧
      Reduce t2 m1 (e2.subst (Subst.unpack cs (.free y))) m' X ∧ t = t1 ++ t2) := by
  generalize hgen : Exp.unpack e1 e2 = efull at hred
  induction hred generalizing e1 with
  | refl => exact Or.inl ⟨e1, Reduce.refl, hgen.symm⟩
  | step hstep rest ih =>
    rw [←hgen] at hstep
    cases hstep with
    | step_ctx_unpack hstep1 =>
      rcases ih rfl with ⟨e1', hr, hX⟩ | ⟨t1, t2, m1, cs, y, hr1, hr2, ht⟩
      · exact Or.inl ⟨e1', Reduce.step hstep1 hr, hX⟩
      · exact Or.inr ⟨_, t2, m1, cs, y, Reduce.step hstep1 hr1, hr2,
          by rw [ht, List.append_assoc]⟩
    | step_unpack =>
      exact Or.inr ⟨[], _, _, _, _, Reduce.refl, rest, rfl⟩

/-! ## Progress and authorization along reductions -/

/-- **Progress along reductions**: every state reachable from a safe configuration
  within the read budget is progressive.  Proven by consulting the `Safe` derivation in
  place and decomposing the given reduction against it, paying budget as the
  decomposition crosses the head boundary of a `letin`/`unpack`. -/
theorem safe_reduce_progressive {k : Nat} {R : CapabilitySet} {m : Memory} {e : Exp {}}
    (h : Safe k R m e) :
    ∀ {t : Trace} {m' : Memory} {e' : Exp {}},
      Reduce t m e m' e' -> t.readCount < k -> IsProgressive m' e' := by
  induction h with
  | exhausted =>
    intro t m' e' _ hbud
    exact absurd hbud (Nat.not_lt_zero _)
  | ans hans =>
    intro t m' e' hred _
    obtain ⟨rfl, rfl, rfl⟩ := reduce_ans_eq hans hred
    exact IsProgressive.done hans
  | alloc hlk =>
    intro t m' e' hred _
    cases hred with
    | refl =>
      obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
      exact IsProgressive.step (Step.step_alloc (l := l) hlk hfresh)
    | step hstep rest =>
      cases hstep with
      | step_alloc hlk2 hfresh2 =>
        obtain ⟨rfl, rfl, rfl⟩ := reduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.pack) rest
        exact IsProgressive.done (Exp.IsAns.is_val Exp.IsVal.pack)
  | apply hlk _ ih =>
    intro t m' e' hred hbud
    cases hred with
    | refl => exact IsProgressive.step (Step.step_apply hlk)
    | step hstep rest =>
      cases hstep with
      | step_apply hlk2 =>
        have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
        simp only at heq
        cases heq
        exact ih rest (by simpa using hbud)
      | step_invoke hlkx _ =>
        rw [hlk] at hlkx
        exact absurd hlkx (by simp)
  | invoke _ hlkx hlky =>
    intro t m' e' hred _
    cases hred with
    | refl => exact IsProgressive.step (Step.step_invoke hlkx hlky)
    | step hstep rest =>
      cases hstep with
      | step_apply hlk2 => rw [hlkx] at hlk2; exact absurd hlk2 (by simp)
      | step_invoke _ _ =>
        obtain ⟨rfl, rfl, rfl⟩ := reduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.unit) rest
        exact IsProgressive.done (Exp.IsAns.is_val Exp.IsVal.unit)
  | tapply hlk _ ih =>
    intro t m' e' hred hbud
    cases hred with
    | refl => exact IsProgressive.step (Step.step_tapply hlk)
    | step hstep rest =>
      cases hstep with
      | step_tapply hlk2 =>
        have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
        simp only at heq
        cases heq
        exact ih rest (by simpa using hbud)
  | capply hlk _ ih =>
    intro t m' e' hred hbud
    cases hred with
    | refl => exact IsProgressive.step (Step.step_capply hlk)
    | step hstep rest =>
      cases hstep with
      | step_capply hlk2 =>
        have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
        simp only at heq
        cases heq
        exact ih rest (by simpa using hbud)
  | letin hse1 h_ans h_val h_var ih1 ihval ihvar =>
    intro t m' e' hred hbud
    rcases reduce_letin_split hred with ⟨e1', hr, rfl⟩ |
      ⟨t1, t2, m1, y, hr1, hr2, rfl⟩ |
      ⟨t1, t2, m1, v, hv, hwf, l, hfresh, hr1, hr2, rfl⟩
    · cases ih1 hr hbud with
      | step hstep => exact IsProgressive.step (Step.step_ctx_letin hstep)
      | done hans1 =>
        obtain ⟨hsa, hwfv⟩ := h_ans _ _ _ (reduce_to_bigstep hr hans1) hbud
        rcases Exp.isSimpleAns_cases hsa with hv | ⟨n, rfl⟩
        · obtain ⟨l0, hfresh⟩ := Memory.exists_fresh _
          exact IsProgressive.step (Step.step_lift (l := l0) hv hwfv hfresh)
        · exact IsProgressive.step Step.step_rename
    · have hbs1 := reduce_to_bigstep hr1 Exp.IsAns.is_var
      rw [Trace.readCount_append] at hbud
      exact ihvar hbs1 hr2 (by omega)
    · have hbs1 := reduce_to_bigstep hr1 (Exp.IsAns.is_val (Exp.IsVal.of_simple hv))
      rw [Trace.readCount_append] at hbud
      exact ihval hbs1 hv hwf l hfresh hr2 (by omega)
  | unpack hse1 h_ans h_val ih1 ihval =>
    intro t m' e' hred hbud
    rcases reduce_unpack_split hred with ⟨e1', hr, rfl⟩ |
      ⟨t1, t2, m1, cs, y, hr1, hr2, rfl⟩
    · cases ih1 hr hbud with
      | step hstep => exact IsProgressive.step (Step.step_ctx_unpack hstep)
      | done hans1 =>
        obtain ⟨hpk, _⟩ := h_ans _ _ _ (reduce_to_bigstep hr hans1) hbud
        obtain ⟨cs', n, rfl⟩ := Exp.isPack_cases hpk
        exact IsProgressive.step Step.step_unpack
    · have hbs1 := reduce_to_bigstep hr1 (Exp.IsAns.is_val Exp.IsVal.pack)
      rw [Trace.readCount_append] at hbud
      exact ihval hbs1 hr2 (by omega)
  | read _ hlk =>
    intro t m' e' hred _
    cases hred with
    | refl => exact IsProgressive.step (Step.step_read hlk)
    | step hstep rest =>
      cases hstep with
      | step_read _ =>
        obtain ⟨rfl, rfl, rfl⟩ := reduce_ans_eq Exp.IsAns.is_var rest
        exact IsProgressive.done Exp.IsAns.is_var
  | write _ hx hy =>
    intro t m' e' hred _
    cases hred with
    | refl => exact IsProgressive.step (Step.step_write hx hy)
    | step hstep rest =>
      cases hstep with
      | step_write _ _ =>
        obtain ⟨rfl, rfl, rfl⟩ := reduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.unit) rest
        exact IsProgressive.done (Exp.IsAns.is_val Exp.IsVal.unit)
  | cond hres h_true h_false ihtrue ihfalse =>
    intro t m' e' hred hbud
    cases hred with
    | refl =>
      exact safe_implies_progressive (Safe.cond hres h_true h_false) (by simpa using hbud)
    | step hstep rest =>
      cases hstep with
      | step_cond_var_true hlk =>
        exact ihtrue (resolve_of_lookup hlk) rest (by simpa using hbud)
      | step_cond_var_false hlk =>
        exact ihfalse (resolve_of_lookup hlk) rest (by simpa using hbud)

/-- **Authorization along reductions**: every within-budget partial run of a safe
  configuration only uses capabilities in its authority (or cells it allocated). -/
theorem safe_reduce_traceok {k : Nat} {R : CapabilitySet} {m : Memory} {e : Exp {}}
    (h : Safe k R m e) :
    ∀ {t : Trace} {m' : Memory} {e' : Exp {}},
      Reduce t m e m' e' -> t.readCount < k -> TraceOk t R := by
  induction h with
  | exhausted =>
    intro t m' e' _ hbud
    exact absurd hbud (Nat.not_lt_zero _)
  | ans hans =>
    intro t m' e' hred _
    obtain ⟨rfl, rfl, rfl⟩ := reduce_ans_eq hans hred
    exact TraceOk.nil
  | alloc hlk =>
    intro t m' e' hred _
    cases hred with
    | refl => exact TraceOk.nil
    | step hstep rest =>
      cases hstep with
      | step_alloc hlk2 hfresh2 =>
        obtain ⟨rfl, rfl, rfl⟩ := reduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.pack) rest
        exact TraceOk.alloc
  | apply hlk _ ih =>
    intro t m' e' hred hbud
    cases hred with
    | refl => exact TraceOk.nil
    | step hstep rest =>
      cases hstep with
      | step_apply hlk2 =>
        have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
        simp only at heq
        cases heq
        simpa using ih rest (by simpa using hbud)
      | step_invoke hlkx _ =>
        rw [hlk] at hlkx
        exact absurd hlkx (by simp)
  | invoke hmem hlkx hlky =>
    intro t m' e' hred _
    cases hred with
    | refl => exact TraceOk.nil
    | step hstep rest =>
      cases hstep with
      | step_apply hlk2 => rw [hlkx] at hlk2; exact absurd hlk2 (by simp)
      | step_invoke _ _ =>
        obtain ⟨rfl, rfl, rfl⟩ := reduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.unit) rest
        exact TraceOk.access hmem
  | tapply hlk _ ih =>
    intro t m' e' hred hbud
    cases hred with
    | refl => exact TraceOk.nil
    | step hstep rest =>
      cases hstep with
      | step_tapply hlk2 =>
        have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
        simp only at heq
        cases heq
        simpa using ih rest (by simpa using hbud)
  | capply hlk _ ih =>
    intro t m' e' hred hbud
    cases hred with
    | refl => exact TraceOk.nil
    | step hstep rest =>
      cases hstep with
      | step_capply hlk2 =>
        have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
        simp only at heq
        cases heq
        simpa using ih rest (by simpa using hbud)
  | letin hse1 h_ans h_val h_var ih1 ihval ihvar =>
    intro t m' e' hred hbud
    rcases reduce_letin_split hred with ⟨e1', hr, rfl⟩ |
      ⟨t1, t2, m1, y, hr1, hr2, rfl⟩ |
      ⟨t1, t2, m1, v, hv, hwf, l, hfresh, hr1, hr2, rfl⟩
    · exact ih1 hr hbud
    · have hbs1 := reduce_to_bigstep hr1 Exp.IsAns.is_var
      rw [Trace.readCount_append] at hbud
      exact TraceOk.append (ih1 hr1 (by omega)) (ihvar hbs1 hr2 (by omega))
    · have hbs1 := reduce_to_bigstep hr1 (Exp.IsAns.is_val (Exp.IsVal.of_simple hv))
      rw [Trace.readCount_append] at hbud
      exact TraceOk.append (ih1 hr1 (by omega)) (ihval hbs1 hv hwf l hfresh hr2 (by omega))
  | unpack hse1 h_ans h_val ih1 ihval =>
    intro t m' e' hred hbud
    rcases reduce_unpack_split hred with ⟨e1', hr, rfl⟩ |
      ⟨t1, t2, m1, cs, y, hr1, hr2, rfl⟩
    · exact ih1 hr hbud
    · have hbs1 := reduce_to_bigstep hr1 (Exp.IsAns.is_val Exp.IsVal.pack)
      rw [Trace.readCount_append] at hbud
      exact TraceOk.append (ih1 hr1 (by omega)) (ihval hbs1 hr2 (by omega))
  | read hmem hlk =>
    intro t m' e' hred _
    cases hred with
    | refl => exact TraceOk.nil
    | step hstep rest =>
      cases hstep with
      | step_read _ =>
        obtain ⟨rfl, rfl, rfl⟩ := reduce_ans_eq Exp.IsAns.is_var rest
        exact TraceOk.read hmem
  | write hmem hx hy =>
    intro t m' e' hred _
    cases hred with
    | refl => exact TraceOk.nil
    | step hstep rest =>
      cases hstep with
      | step_write _ _ =>
        obtain ⟨rfl, rfl, rfl⟩ := reduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.unit) rest
        exact TraceOk.access hmem
  | cond hres h_true h_false ihtrue ihfalse =>
    intro t m' e' hred hbud
    cases hred with
    | refl => exact TraceOk.nil
    | step hstep rest =>
      cases hstep with
      | step_cond_var_true hlk =>
        simpa using ihtrue (resolve_of_lookup hlk) rest (by simpa using hbud)
      | step_cond_var_false hlk =>
        simpa using ihfalse (resolve_of_lookup hlk) rest (by simpa using hbud)

/-- Opening a `letin` on a variable answer. -/
theorem reduce_rename_var {t : Trace} {m1 m2 : Memory} {x : Var .var {}} {e2 : Exp ({},x)}
    {v : Exp {}}
    (h : Reduce t m1 (e2.subst (Subst.openVar x)) m2 v) :
    Reduce t m1 (.letin (.var x) e2) m2 v := by
  obtain ⟨y, rfl⟩ := Var.free_cases x
  simpa using Reduce.step Step.step_rename h

/-- Opening an `unpack` on a pack answer. -/
theorem reduce_unpack_pack {t : Trace} {m1 m2 : Memory} {x : Var .var {}}
    {cs : CaptureSet {}} {e2 : Exp ({},C,x)} {v : Exp {}}
    (h : Reduce t m1 (e2.subst (Subst.unpack cs x)) m2 v) :
    Reduce t m1 (.unpack (.pack cs x) e2) m2 v := by
  obtain ⟨y, rfl⟩ := Var.free_cases x
  simpa using Reduce.step Step.step_unpack h

/-- Big-step ⇒ small-step: every `BigStep` run is realized by a `Reduce` with the same
  trace. -/
theorem bigstep_to_reduce {m : Memory} {e : Exp {}} {t : Trace} {v : Exp {}} {m' : Memory}
    (hbs : BigStep m e t v m') : Reduce t m e m' v := by
  induction hbs with
  | bs_pack => exact Reduce.refl
  | bs_val _ => exact Reduce.refl
  | bs_var => exact Reduce.refl
  | bs_apply hlk _ ih => simpa using Reduce.step (Step.step_apply hlk) ih
  | bs_invoke hlkx hlky => simpa using Reduce.step (Step.step_invoke hlkx hlky) Reduce.refl
  | bs_tapply hlk _ ih => simpa using Reduce.step (Step.step_tapply hlk) ih
  | bs_capply hlk _ ih => simpa using Reduce.step (Step.step_capply hlk) ih
  | bs_letin_val _ hv hwf hfresh _ ih1 ih2 =>
    simpa using reduce_trans (reduce_ctx_letin ih1) (Reduce.step (Step.step_lift hv hwf hfresh) ih2)
  | bs_letin_var _ _ ih1 ih2 =>
    exact reduce_trans (reduce_ctx_letin ih1) (reduce_rename_var ih2)
  | bs_unpack _ _ ih1 ih2 =>
    exact reduce_trans (reduce_ctx_unpack ih1) (reduce_unpack_pack ih2)
  | bs_read hlk => simpa using Reduce.step (Step.step_read hlk) Reduce.refl
  | bs_write hx hy => simpa using Reduce.step (Step.step_write hx hy) Reduce.refl
  | bs_alloc hx hfresh => simpa using Reduce.step (Step.step_alloc hx hfresh) Reduce.refl
  | bs_cond_true hres _ ih =>
    obtain ⟨fx, hv, R0, rfl, hlk⟩ := resolve_var_inv hres
    simpa using Reduce.step (Step.step_cond_var_true (hv := hv) (R := R0) hlk) ih
  | bs_cond_false hres _ ih =>
    obtain ⟨fx, hv, R0, rfl, hlk⟩ := resolve_var_inv hres
    simpa using Reduce.step (Step.step_cond_var_false (hv := hv) (R := R0) hlk) ih

/-- Full authorization of an evaluated answer: a `BigStep` run of a safe configuration
  within budget is authorized. -/
theorem safe_bigstep_traceok {k : Nat} {R : CapabilitySet} {m : Memory} {e : Exp {}}
    {t : Trace} {v : Exp {}} {m' : Memory}
    (h : Safe k R m e) (hbs : BigStep m e t v m') (hbud : t.readCount < k) :
    TraceOk t R :=
  safe_reduce_traceok h (bigstep_to_reduce hbs) hbud

end CC
