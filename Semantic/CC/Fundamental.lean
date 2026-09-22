import Semantic.CC.Denotation
import Semantic.CC.Semantics

namespace CC

/-! ## Variables -/

theorem typed_env_lookup_var
  (hts : EnvTyping Γ env k st m)
  (hx : Ctx.LookupVar Γ x T) :
  Ty.capt_val_denot env T k st m (.var (.free (env.lookup_var x))) := by
  induction hx generalizing m
  case here =>
    rename_i Γ0 T0
    cases env; rename_i info0 env0
    cases info0; rename_i n
    unfold EnvTyping at hts
    simp only [TypeEnv.lookup_var, TypeEnv.lookup]
    exact IDenot.equiv_ltr (weaken_capt_val_denot (env:=env0) (x:=n) (T:=T0)) hts.1
  case there b =>
    rename_i k' Γ0 x0 T0 binding hlk
    cases binding
    case var =>
      rename_i Tb
      cases env; rename_i info0 env0
      cases info0; rename_i n
      unfold EnvTyping at hts
      obtain ⟨_, henv0⟩ := hts
      simp only [TypeEnv.lookup_var, TypeEnv.lookup]
      exact IDenot.equiv_ltr (weaken_capt_val_denot (env:=env0) (x:=n) (T:=T0)) (b henv0)
    case tvar =>
      rename_i Sb
      cases env; rename_i info0 env0
      cases info0; rename_i d
      unfold EnvTyping at hts
      obtain ⟨_, _, henv0⟩ := hts
      simp only [TypeEnv.lookup_var, TypeEnv.lookup]
      exact IDenot.equiv_ltr (tweaken_capt_val_denot (env:=env0) (d:=d) (T:=T0)) (b henv0)
    case cvar =>
      rename_i Bb
      cases env; rename_i info0 env0
      cases info0; rename_i cs
      unfold EnvTyping at hts
      obtain ⟨_, _, _, henv0⟩ := hts
      simp only [TypeEnv.lookup_var, TypeEnv.lookup]
      exact IDenot.equiv_ltr (cweaken_capt_val_denot (env:=env0) (cs:=cs) (T:=T0)) (b henv0)

theorem typed_env_lookup_var_reachability
  (hts : EnvTyping Γ env k st m)
  (hx : Ctx.LookupVar Γ x T) :
  reachability_of_loc m.heap (env.lookup_var x) ⊆ T.captureSet.denot env m := by
  induction hx generalizing m
  case here =>
    rename_i Γ' T'
    cases env; rename_i info' env'
    cases info'; rename_i n
    unfold EnvTyping at hts
    simp only [TypeEnv.lookup_var, TypeEnv.lookup]
    cases T' with | capt C S =>
    have hval := hts.1
    rw [capt_val_denot_capt] at hval
    obtain ⟨_, _, _, hshape⟩ := hval
    have hsafe := shape_val_denot_is_reachability_safe
      (typed_env_is_reachability_safe hts.2) S
    have hreach := hsafe (C.denot env' m) k st m (.var (.free n)) hshape
    change reachability_of_loc m.heap n ⊆ C.denot env' m at hreach
    change
      reachability_of_loc m.heap n ⊆
        (C.rename Rename.succ).denot (env'.extend (TypeInfo.var n)) m
    have hreb := rebind_captureset_denot (Rebind.weaken (env:=env') (x:=n)) C
    have hreb_m : C.denot env' m =
      (C.rename Rename.succ).denot (env'.extend (TypeInfo.var n)) m := by
      rw [hreb]
      rfl
    rw [<-hreb_m]
    exact hreach
  case there b hx_prev ih =>
    cases b
    case var =>
      rename_i Γ' x' T' Tb
      cases env; rename_i info' env'
      cases info'; rename_i n
      unfold EnvTyping at hts
      obtain ⟨_, henv'⟩ := hts
      have hih := ih henv'
      simp only [TypeEnv.lookup_var, TypeEnv.lookup]
      cases T' with | capt C S =>
      change
        reachability_of_loc m.heap (env'.lookup_var x') ⊆
          (C.rename Rename.succ).denot (env'.extend (TypeInfo.var n)) m
      change reachability_of_loc m.heap (env'.lookup_var x') ⊆ C.denot env' m at hih
      have hreb := rebind_captureset_denot
        (Rebind.weaken (env:=env') (x:=n)) C
      have hreb_m : C.denot env' m =
        (C.rename Rename.succ).denot (env'.extend (TypeInfo.var n)) m := by
        rw [hreb]
        rfl
      rw [<-hreb_m]
      exact hih
    case tvar =>
      rename_i Γ' x' T' Sb
      cases env; rename_i info' env'
      cases info'; rename_i d
      unfold EnvTyping at hts
      obtain ⟨_, _, henv'⟩ := hts
      have hih := ih henv'
      simp only [TypeEnv.lookup_var, TypeEnv.lookup]
      cases T' with | capt C S =>
      change
        reachability_of_loc m.heap (env'.lookup_var x') ⊆
          (C.rename Rename.succ).denot (env'.extend (TypeInfo.tvar d)) m
      change reachability_of_loc m.heap (env'.lookup_var x') ⊆ C.denot env' m at hih
      have hreb := rebind_captureset_denot
        (Rebind.tweaken (env:=env') (d:=d)) C
      have hreb_m : C.denot env' m =
        (C.rename Rename.succ).denot (env'.extend (TypeInfo.tvar d)) m := by
        rw [hreb]
        rfl
      rw [<-hreb_m]
      exact hih
    case cvar =>
      rename_i Γ' x' T' Bb
      cases env; rename_i info' env'
      cases info'; rename_i cs
      unfold EnvTyping at hts
      obtain ⟨_, _, _, henv'⟩ := hts
      have hih := ih henv'
      simp only [TypeEnv.lookup_var, TypeEnv.lookup]
      cases T' with | capt C S =>
      change
        reachability_of_loc m.heap (env'.lookup_var x') ⊆
          (C.rename Rename.succ).denot (env'.extend (TypeInfo.cvar cs)) m
      change reachability_of_loc m.heap (env'.lookup_var x') ⊆ C.denot env' m at hih
      have hreb := rebind_captureset_denot
        (Rebind.cweaken (env:=env') (cs:=cs)) C
      have hreb_m : C.denot env' m =
        (C.rename Rename.succ).denot (env'.extend (TypeInfo.cvar cs)) m := by
        rw [hreb]
        rfl
      rw [<-hreb_m]
      exact hih

theorem shape_denot_with_var_reachability
  {C : CaptureSet s} {S : Ty .shape s}
  (hts : EnvTyping Γ env k st m)
  (hd : Ty.shape_val_denot env S (C.denot env m) k st m (.var (.free (env.lookup_var x)))) :
  Ty.shape_val_denot env S (reachability_of_loc m.heap (env.lookup_var x)) k st m
    (.var (.free (env.lookup_var x))) :=
  shape_val_denot_is_tight (typed_env_is_tight hts) S (C.denot env m) k st m (env.lookup_var x) hd

theorem sem_typ_var
  (hx : Γ.LookupVar x (.capt C S)) :
  (.var (.bound x)) # Γ ⊨ (.var (.bound x)) : (.typ (.capt (.var (.bound x)) S)) := by
  intro env k st m hts
  change ExpDenot _ _ _ _ _ (.var (.free (env.lookup_var x)))
  apply ExpDenot.ans_intro_same Exp.IsAns.is_var pack_bound_of_var
  intro _
  have h_lookup := typed_env_lookup_var hts hx
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h_lookup ⊢
  obtain ⟨hsimple, hwf, hwf_C, hshape⟩ := h_lookup
  refine ⟨hsimple, hwf, ?_, ?_⟩
  · change (CaptureSet.var (.free (env.lookup_var x))).WfInHeap m.heap
    cases hwf with
    | wf_var hwf_var =>
      cases hwf_var with
      | wf_free hlookup =>
        exact CaptureSet.WfInHeap.wf_var_free hlookup
  · simp only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
      CaptureSet.ground_denot]
    exact shape_denot_with_var_reachability hts hshape

theorem expand_captures_eq_ground_denot (cs : CaptureSet {}) (m : Memory) :
  expand_captures m.heap cs = cs.ground_denot m := by
  induction cs with
  | empty => rfl
  | var v =>
    cases v with
    | free x => rfl
    | bound bv => cases bv
  | cvar cv => cases cv
  | union cs1 cs2 ih1 ih2 =>
    simp [expand_captures, CaptureSet.ground_denot, ih1, ih2]

/-- The denotation of a closed capture set does not depend on the memory. -/
theorem closed_capture_denot_monotonic {C : CaptureSet s} {env : TypeEnv s}
    {k : Nat} {st : StoreTyping k} {m m' : Memory}
    (hclosed : C.IsClosed) (hts : EnvTyping Γ env k st m) (hsub : m'.subsumes m) :
    C.denot env m = C.denot env m' :=
  capture_set_denot_is_monotonic
    (CaptureSet.wf_subst (CaptureSet.wf_of_closed hclosed) (from_TypeEnv_wf_in_heap hts)) hsub

/-! ## Value introduction forms -/

theorem sem_typ_abs {T2 : Ty TySort.exi (s,x)} {Cf : CaptureSet s}
  (hclosed_abs : (Exp.abs Cf T1 e).IsClosed)
  (ht : (Cf.rename Rename.succ ∪ .var (.bound .here)) # Γ,x:T1 ⊨ e : T2) :
  ∅ # Γ ⊨ Exp.abs Cf T1 e : .typ (Ty.capt Cf (T1.arrow T2)) := by
  intro env k st m hts
  have hCf_closed : Cf.IsClosed := by cases hclosed_abs; assumption
  have hwf_abs : (Exp.abs (Cf.subst (Subst.from_TypeEnv env))
      (T1.subst (Subst.from_TypeEnv env))
      (e.subst (Subst.from_TypeEnv env).lift)).WfInHeap m.heap := by
    simpa [Exp.subst] using
      (Exp.wf_subst (e := Exp.abs Cf T1 e) (σ := Subst.from_TypeEnv env) (H := m.heap)
        (Exp.wf_of_closed hclosed_abs) (from_TypeEnv_wf_in_heap hts))
  have hwf_Cf : (Cf.subst (Subst.from_TypeEnv env)).WfInHeap m.heap :=
    CaptureSet.wf_subst (CaptureSet.wf_of_closed hCf_closed) (from_TypeEnv_wf_in_heap hts)
  change ExpDenot _ _ _ _ _ (Exp.abs (Cf.subst (Subst.from_TypeEnv env))
    (T1.subst (Subst.from_TypeEnv env)) (e.subst (Subst.from_TypeEnv env).lift))
  apply ExpDenot.ans_intro_same (Exp.IsAns.is_val Exp.IsVal.abs)
    (pack_bound_of_simple Exp.IsSimpleVal.abs)
  intro _
  simp only [Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  refine ⟨Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.abs, hwf_abs, hwf_Cf, hwf_abs,
    Cf.subst (Subst.from_TypeEnv env), T1.subst (Subst.from_TypeEnv env),
    e.subst (Subst.from_TypeEnv env).lift, by simp [resolve], hwf_Cf, ?_, ?_⟩
  · rw [expand_captures_eq_ground_denot]
    exact CapabilitySet.Subset.refl
  · intro j hjk st' m' arg hwle harg
    have hsubsume : m'.subsumes m := hwle.1
    have hkey := @Exp.from_TypeEnv_weaken_open s env arg e
    refine hkey ▸ ?_
    have henv : EnvTyping (Γ,x:T1) (env.extend_var arg) j st' m' :=
      ⟨harg, env_typing_worldle_trunc hjk hts hwle⟩
    have this := ht (env.extend_var arg) j st' m' henv
    have hcap_rename :
      (Cf.rename Rename.succ).denot (env.extend_var arg) = Cf.denot env :=
      (rebind_captureset_denot (Rebind.weaken (env:=env) (x:=arg)) Cf).symm
    have hcap_var :
      (CaptureSet.var (.bound .here)).denot (env.extend_var arg) m'
      = reachability_of_loc m'.heap arg := by
      simp [CaptureSet.denot, CaptureSet.ground_denot, CaptureSet.subst,
            Subst.from_TypeEnv, Var.subst, TypeEnv.lookup_var]
      rfl
    have hCf_mono : Cf.denot env m = Cf.denot env m' :=
      closed_capture_denot_monotonic hCf_closed hts hsubsume
    have hauthority :
      (Cf.rename Rename.succ ∪ .var (.bound .here)).denot (env.extend_var arg) m' =
      expand_captures m.heap (Cf.subst (Subst.from_TypeEnv env)) ∪
        reachability_of_loc m'.heap arg := by
      calc (Cf.rename Rename.succ ∪ .var (.bound .here)).denot (env.extend_var arg) m'
        _ = (Cf.rename Rename.succ).denot (env.extend_var arg) m' ∪
            (CaptureSet.var (.bound .here)).denot (env.extend_var arg) m' := by
          simp [CaptureSet.denot, CaptureSet.ground_denot, CaptureSet.subst]
        _ = Cf.denot env m' ∪ reachability_of_loc m'.heap arg := by
          rw [congrFun hcap_rename m', hcap_var]
        _ = Cf.denot env m ∪ reachability_of_loc m'.heap arg := by
          rw [← hCf_mono]
        _ = (Cf.subst (Subst.from_TypeEnv env)).ground_denot m ∪
            reachability_of_loc m'.heap arg := by
          simp [CaptureSet.denot]
        _ = expand_captures m.heap (Cf.subst (Subst.from_TypeEnv env)) ∪
            reachability_of_loc m'.heap arg := by
          rw [← expand_captures_eq_ground_denot]
    rw [← hauthority]
    exact this

theorem sem_typ_tabs {T : Ty TySort.exi (s,X)} {Cf : CaptureSet s}
  (hclosed_tabs : (Exp.tabs Cf S e).IsClosed)
  (ht : Cf.rename Rename.succ # (Γ,X<:S) ⊨ e : T) :
  ∅ # Γ ⊨ Exp.tabs Cf S e : .typ (Ty.capt Cf (S.poly T)) := by
  intro env k st m hts
  have hCf_closed : Cf.IsClosed := by cases hclosed_tabs; assumption
  have hwf_tabs : (Exp.tabs (Cf.subst (Subst.from_TypeEnv env))
      (S.subst (Subst.from_TypeEnv env))
      (e.subst (Subst.from_TypeEnv env).lift)).WfInHeap m.heap := by
    simpa [Exp.subst] using
      (Exp.wf_subst (e := Exp.tabs Cf S e) (σ := Subst.from_TypeEnv env) (H := m.heap)
        (Exp.wf_of_closed hclosed_tabs) (from_TypeEnv_wf_in_heap hts))
  have hwf_Cf : (Cf.subst (Subst.from_TypeEnv env)).WfInHeap m.heap :=
    CaptureSet.wf_subst (CaptureSet.wf_of_closed hCf_closed) (from_TypeEnv_wf_in_heap hts)
  change ExpDenot _ _ _ _ _ (Exp.tabs (Cf.subst (Subst.from_TypeEnv env))
    (S.subst (Subst.from_TypeEnv env)) (e.subst (Subst.from_TypeEnv env).lift))
  apply ExpDenot.ans_intro_same (Exp.IsAns.is_val Exp.IsVal.tabs)
    (pack_bound_of_simple Exp.IsSimpleVal.tabs)
  intro _
  simp only [Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  refine ⟨Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.tabs, hwf_tabs, hwf_Cf, hwf_tabs,
    Cf.subst (Subst.from_TypeEnv env), S.subst (Subst.from_TypeEnv env),
    e.subst (Subst.from_TypeEnv env).lift, by simp [resolve], hwf_Cf, ?_, ?_⟩
  · rw [expand_captures_eq_ground_denot]
    exact CapabilitySet.Subset.refl
  · intro j hjk st' m' denot hwle hproper himply
    have hsubsume : m'.subsumes m := hwle.1
    have hkey := @Exp.from_TypeEnv_weaken_open_tvar s env denot e
    refine hkey ▸ ?_
    have henv : EnvTyping (Γ,X<:S) (env.extend_tvar denot) j st' m' :=
      ⟨hproper, himply, env_typing_worldle_trunc hjk hts hwle⟩
    have this := ht (env.extend_tvar denot) j st' m' henv
    have hcap_rename :
      (Cf.rename Rename.succ).denot (env.extend_tvar denot) = Cf.denot env :=
      (rebind_captureset_denot (Rebind.tweaken (env:=env) (d:=denot)) Cf).symm
    have hCf_mono : Cf.denot env m = Cf.denot env m' :=
      closed_capture_denot_monotonic hCf_closed hts hsubsume
    have hauthority :
      (Cf.rename Rename.succ).denot (env.extend_tvar denot) m' =
      expand_captures m.heap (Cf.subst (Subst.from_TypeEnv env)) := by
      calc (Cf.rename Rename.succ).denot (env.extend_tvar denot) m'
        _ = Cf.denot env m' := by rw [congrFun hcap_rename m']
        _ = Cf.denot env m := by rw [← hCf_mono]
        _ = (Cf.subst (Subst.from_TypeEnv env)).ground_denot m := by
          simp [CaptureSet.denot]
        _ = expand_captures m.heap (Cf.subst (Subst.from_TypeEnv env)) := by
          rw [← expand_captures_eq_ground_denot]
    rw [← hauthority]
    exact this

theorem sem_typ_cabs {T : Ty TySort.exi (s,C)} {Cf : CaptureSet s}
  (hclosed_cabs : (Exp.cabs Cf cb e).IsClosed)
  (ht : Cf.rename Rename.succ # Γ,C<:cb ⊨ e : T) :
  ∅ # Γ ⊨ Exp.cabs Cf cb e : .typ (Ty.capt Cf (Ty.cpoly cb T)) := by
  intro env k st m hts
  have hCf_closed : Cf.IsClosed := by cases hclosed_cabs; assumption
  have hcb_closed : cb.IsClosed := by cases hclosed_cabs; assumption
  have hwf_cabs : (Exp.cabs (Cf.subst (Subst.from_TypeEnv env))
      (cb.subst (Subst.from_TypeEnv env))
      (e.subst (Subst.from_TypeEnv env).lift)).WfInHeap m.heap := by
    simpa [Exp.subst] using
      (Exp.wf_subst (e := Exp.cabs Cf cb e) (σ := Subst.from_TypeEnv env) (H := m.heap)
        (Exp.wf_of_closed hclosed_cabs) (from_TypeEnv_wf_in_heap hts))
  have hwf_Cf : (Cf.subst (Subst.from_TypeEnv env)).WfInHeap m.heap :=
    CaptureSet.wf_subst (CaptureSet.wf_of_closed hCf_closed) (from_TypeEnv_wf_in_heap hts)
  change ExpDenot _ _ _ _ _ (Exp.cabs (Cf.subst (Subst.from_TypeEnv env))
    (cb.subst (Subst.from_TypeEnv env)) (e.subst (Subst.from_TypeEnv env).lift))
  apply ExpDenot.ans_intro_same (Exp.IsAns.is_val Exp.IsVal.cabs)
    (pack_bound_of_simple Exp.IsSimpleVal.cabs)
  intro _
  simp only [Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  refine ⟨Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.cabs, hwf_cabs, hwf_Cf, hwf_cabs,
    Cf.subst (Subst.from_TypeEnv env), cb.subst (Subst.from_TypeEnv env),
    e.subst (Subst.from_TypeEnv env).lift, by simp [resolve], hwf_Cf, ?_, ?_⟩
  · rw [expand_captures_eq_ground_denot]
    exact CapabilitySet.Subset.refl
  · intro j hjk st' m' CS hwf hwle hsub_bound
    have hsubsume : m'.subsumes m := hwle.1
    have hts' := env_typing_worldle_trunc hjk hts hwle
    have hkey := @Exp.from_TypeEnv_weaken_open_cvar s env CS e
    refine hkey ▸ ?_
    have henv : EnvTyping (Γ,C<:cb) (env.extend_cvar CS) j st' m' := by
      refine ⟨hwf, ?_, ?_, hts'⟩
      · exact CaptureBound.wf_subst (CaptureBound.wf_of_closed hcb_closed)
          (from_TypeEnv_wf_in_heap hts')
      · have heq : CS.ground_denot = CaptureSet.denot TypeEnv.empty CS := by
          funext mm
          simp [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id]
        rw [heq]
        exact hsub_bound
    have this := ht (env.extend_cvar CS) j st' m' henv
    have hcap_rename :
      (Cf.rename Rename.succ).denot (env.extend_cvar CS) = Cf.denot env :=
      (rebind_captureset_denot (Rebind.cweaken (env:=env) (cs:=CS)) Cf).symm
    have hCf_mono : Cf.denot env m = Cf.denot env m' :=
      closed_capture_denot_monotonic hCf_closed hts hsubsume
    have hauthority :
      (Cf.rename Rename.succ).denot (env.extend_cvar CS) m' =
      expand_captures m.heap (Cf.subst (Subst.from_TypeEnv env)) := by
      calc (Cf.rename Rename.succ).denot (env.extend_cvar CS) m'
        _ = Cf.denot env m' := by rw [congrFun hcap_rename m']
        _ = Cf.denot env m := by rw [← hCf_mono]
        _ = (Cf.subst (Subst.from_TypeEnv env)).ground_denot m := by
          simp [CaptureSet.denot]
        _ = expand_captures m.heap (Cf.subst (Subst.from_TypeEnv env)) := by
          rw [← expand_captures_eq_ground_denot]
    rw [← hauthority]
    exact this

theorem sem_typ_unit :
  {} # Γ ⊨ Exp.unit : .typ (.capt {} .unit) := by
  intro env k st m hts
  change ExpDenot _ _ _ _ _ Exp.unit
  apply ExpDenot.ans_intro_same (Exp.IsAns.is_val Exp.IsVal.unit)
    (pack_bound_of_simple Exp.IsSimpleVal.unit)
  intro _
  exact unit_val_denot env k st m

theorem sem_typ_btrue :
  {} # Γ ⊨ Exp.btrue : .typ (.capt {} .bool) := by
  intro env k st m hts
  change ExpDenot _ _ _ _ _ Exp.btrue
  apply ExpDenot.ans_intro_same (Exp.IsAns.is_val Exp.IsVal.btrue)
    (pack_bound_of_simple Exp.IsSimpleVal.btrue)
  intro _
  exact btrue_val_denot env k st m

theorem sem_typ_bfalse :
  {} # Γ ⊨ Exp.bfalse : .typ (.capt {} .bool) := by
  intro env k st m hts
  change ExpDenot _ _ _ _ _ Exp.bfalse
  apply ExpDenot.ans_intro_same (Exp.IsAns.is_val Exp.IsVal.bfalse)
    (pack_bound_of_simple Exp.IsSimpleVal.bfalse)
  intro _
  exact bfalse_val_denot env k st m


/-! ## Inversion of value denotations -/

theorem var_exp_denot_inv {A : CapabilitySet} {k : Nat} {st : StoreTyping k} {m : Memory}
  {x : Var .var {}}
  (hkpos : 0 < k) (hmt : MemTyped k st m)
  (hv : Ty.exi_exp_denot env T A k st m (.var x)) :
  ∃ st' : StoreTyping k, WorldLe st' m st m ∧ MemTyped k st' m ∧
    Ty.exi_val_denot env T k st' m (.var x) :=
  ExpDenot.var_inv hkpos hmt hv

theorem abs_val_denot_inv {A : CapabilitySet} {k : Nat} {st : StoreTyping k}
  (hv : Ty.shape_val_denot env (.arrow T1 T2) A k st m (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs T0 e0 hval R,
      m.heap fx = some (Cell.val ⟨Exp.abs cs T0 e0, hval, R⟩)
    ∧ expand_captures m.heap cs ⊆ A
    ∧ (∀ (j : Nat) (hjk : j ≤ k) (st' : StoreTyping j) (m' : Memory) (arg : Nat),
      WorldLe st' m' (st.trunc hjk) m ->
      Ty.capt_val_denot env T1 j st' m' (.var (.free arg)) ->
      ExpDenot (Ty.exi_val_denot (env.extend_var arg) T2)
        (expand_captures m.heap cs ∪ (reachability_of_loc m'.heap arg)) j st' m'
        (e0.subst (Subst.openVar (.free arg)))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    unfold Ty.shape_val_denot resolve at hv
    simp only [List.empty_eq] at hv
    obtain ⟨hwf_e, cs, T0, e0, hresolve, hwf_cs, hR0_sub, hfun⟩ := hv
    generalize hres : m.heap fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some cell =>
      cases cell with
      | val hval =>
        cases hval with | mk unwrap isVal reachability =>
        injection hresolve with hunwrap
        subst hunwrap
        exact ⟨fx, rfl, cs, T0, e0, isVal, reachability, hres, hR0_sub, hfun⟩
      | capability => simp at hresolve
      | masked => simp at hresolve

theorem tabs_val_denot_inv {A : CapabilitySet} {k : Nat} {st : StoreTyping k}
  (hv : Ty.shape_val_denot env (.poly S T) A k st m (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs S0 e0 hval R,
      m.heap fx = some (Cell.val ⟨Exp.tabs cs S0 e0, hval, R⟩)
    ∧ expand_captures m.heap cs ⊆ A
    ∧ (∀ (j : Nat) (hjk : j ≤ k) (st' : StoreTyping j) (m' : Memory) (denot : IPreDenot),
      WorldLe st' m' (st.trunc hjk) m ->
      denot.is_proper ->
      denot.ImplyAfter j st' m' (Ty.shape_val_denot env S) ->
      ExpDenot (Ty.exi_val_denot (env.extend_tvar denot) T)
        (expand_captures m.heap cs) j st' m'
        (e0.subst (Subst.openTVar .top))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    unfold Ty.shape_val_denot resolve at hv
    simp only [List.empty_eq] at hv
    obtain ⟨hwf_e, cs, S0, e0, hresolve, hwf_cs, hR0_sub, hfun⟩ := hv
    generalize hres : m.heap fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some cell =>
      cases cell with
      | val hval =>
        cases hval with | mk unwrap isVal reachability =>
        injection hresolve with hunwrap
        subst hunwrap
        exact ⟨fx, rfl, cs, S0, e0, isVal, reachability, hres, hR0_sub, hfun⟩
      | capability => simp at hresolve
      | masked => simp at hresolve

theorem cabs_val_denot_inv {A : CapabilitySet} {k : Nat} {st : StoreTyping k}
  (hv : Ty.shape_val_denot env (.cpoly B T) A k st m (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs B0 e0 hval R,
      m.heap fx = some (Cell.val ⟨Exp.cabs cs B0 e0, hval, R⟩)
    ∧ expand_captures m.heap cs ⊆ A
    ∧ (∀ (j : Nat) (hjk : j ≤ k) (st' : StoreTyping j) (m' : Memory) (CS : CaptureSet {}),
      CS.WfInHeap m'.heap ->
      WorldLe st' m' (st.trunc hjk) m ->
      ((CS.denot TypeEnv.empty m').BoundedBy (B.denot env m')) ->
      ExpDenot (Ty.exi_val_denot (env.extend_cvar CS) T)
        (expand_captures m.heap cs) j st' m'
        (e0.subst (Subst.openCVar CS))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    unfold Ty.shape_val_denot resolve at hv
    simp only [List.empty_eq] at hv
    obtain ⟨hwf_e, cs, B0, e0, hresolve, hwf_cs, hR0_sub, hfun⟩ := hv
    generalize hres : m.heap fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some cell =>
      cases cell with
      | val hval =>
        cases hval with | mk unwrap isVal reachability =>
        injection hresolve with hunwrap
        subst hunwrap
        exact ⟨fx, rfl, cs, B0, e0, isVal, reachability, hres, hR0_sub, hfun⟩
      | capability => simp at hresolve
      | masked => simp at hresolve

theorem cap_val_denot_inv {A : CapabilitySet} {k : Nat} {st : StoreTyping k}
  (hv : Ty.shape_val_denot env .cap A k st m (.var x)) :
  ∃ fx, x = .free fx ∧ m.heap fx = some (.capability .basic) ∧ fx ∈ A := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.shape_val_denot, Memory.lookup] at hv
    obtain ⟨hwf_e, label, heq, hlookup, hmem⟩ := hv
    have : fx = label := by
      injection heq with _ h1
      injection h1
    subst this
    exact ⟨fx, rfl, hlookup, hmem⟩

theorem unit_val_denot_inv {k : Nat} {st : StoreTyping k}
  (hv : Ty.shape_val_denot env .unit A k st m (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ hval R,
      m.heap fx = some (Cell.val ⟨Exp.unit, hval, R⟩) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    unfold Ty.shape_val_denot resolve at hv
    simp only [List.empty_eq] at hv
    generalize hres : m.heap fx = res at hv ⊢
    cases res
    case none => simp at hv
    case some cell =>
      cases cell with
      | val hval =>
        cases hval with | mk unwrap isVal reachability =>
        injection hv with hunwrap
        subst hunwrap
        exact ⟨fx, rfl, isVal, reachability, hres⟩
      | capability => simp at hv
      | masked => simp at hv

theorem cell_val_denot_inv {A : CapabilitySet} {k : Nat} {st : StoreTyping k}
  {T : Ty .capt s}
  (hv : Ty.shape_val_denot env (.cell T) A k st m (.var x)) :
  ∃ (fx n0 : Nat) (Rl : MonRel k), x = .free fx
    ∧ m.lookup fx = some (.capability (.mcell n0))
    ∧ fx ∈ A
    ∧ st.lookup fx = some Rl
    ∧ (∀ (j : Fin k) (w' : StoreTyping j.val) (m' : Memory) (e' : Exp {}),
        Rl j w' m' e' ↔ Ty.capt_val_denot env T j.val w' m' e') := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.shape_val_denot] at hv
    obtain ⟨l, n0, Rl, heq, hlookup, hmem, hst, hbi⟩ := hv
    have : fx = l := by
      injection heq with _ h1
      injection h1
    subst this
    exact ⟨fx, n0, Rl, rfl, hlookup, hmem, hst, hbi⟩

theorem var_subst_is_free {x : BVar s .var} :
  ∃ fx, (Subst.from_TypeEnv env).var x = .free fx := by
  use env.lookup_var x
  rfl

theorem closed_var_inv (x : Var .var {}) :
  ∃ fx, x = .free fx := by
  cases x
  case bound bx => cases bx
  case free fx => use fx

/-- For closed capture sets, the denotation is preserved under substitution with
from_TypeEnv. -/
theorem closed_captureset_subst_denot
  {s : Sig} {env : TypeEnv s} {D : CaptureSet s}
  (hD_closed : D.IsClosed) :
  (D.subst (Subst.from_TypeEnv env)).denot TypeEnv.empty = D.denot env := by
  induction hD_closed with
  | empty =>
    rfl
  | union _ _ ih1 ih2 =>
    simp only [CaptureSet.subst, CaptureSet.denot] at ih1 ih2 ⊢
    funext m
    simp only [CaptureSet.ground_denot]
    rw [congrFun ih1 m, congrFun ih2 m]
  | cvar =>
    simp only [CaptureSet.subst, CaptureSet.denot, Subst.from_TypeEnv]
    change ((env.lookup_cvar _).subst (Subst.from_TypeEnv TypeEnv.empty)).ground_denot =
      (env.lookup_cvar _).ground_denot
    rw [Subst.from_TypeEnv_empty, CaptureSet.subst_id]
  | var_bound =>
    simp only [CaptureSet.subst, CaptureSet.denot, Var.subst, Subst.from_TypeEnv]

/-! ## Pack -/

theorem sem_typ_pack
  {T : Ty .capt (s,C)} {cs : CaptureSet s} {x : Var .var s} {Γ : Ctx s}
  (hclosed_e : (Exp.pack cs x).IsClosed)
  (ht : CaptureSet.var x # Γ ⊨ Exp.var x : (T.subst (Subst.openCVar cs)).typ) :
  CaptureSet.var x # Γ ⊨ Exp.pack cs x : T.exi := by
  intro env k st m hts
  have hclosed_x : x.IsClosed := by
    cases hclosed_e with | pack _ hxc => exact hxc
  have hclosed_cs : cs.IsClosed := by
    cases hclosed_e with | pack hcs_closed _ => exact hcs_closed
  cases hclosed_x
  rename_i bx
  change ExpDenot _ _ _ _ _ (Exp.pack (cs.subst (Subst.from_TypeEnv env))
    (.free (env.lookup_var bx)))
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact ExpDenot.zero
  apply ExpDenot.ans_intro (Exp.IsAns.is_val Exp.IsVal.pack)
  · apply pack_bound_pack
    change reachability_of_loc m.heap (env.lookup_var bx) ⊆
      reachability_of_loc m.heap (env.lookup_var bx)
    exact CapabilitySet.subset_refl
  · intro hmt
    have hx := ht env k st m hts
    obtain ⟨st', hwle, hmt', hval⟩ := ExpDenot.var_inv hkpos hmt hx
    refine ⟨st', hwle, hmt', ?_⟩
    simp only [Ty.exi_val_denot] at hval ⊢
    refine ⟨cs.subst (Subst.from_TypeEnv env), .free (env.lookup_var bx), rfl,
      CaptureSet.wf_subst (CaptureSet.wf_of_closed hclosed_cs) (from_TypeEnv_wf_in_heap hts), ?_⟩
    have hretype := @retype_capt_val_denot (s,C) s
      (env.extend_cvar (cs.subst (Subst.from_TypeEnv env)))
      (Subst.openCVar cs) env
      (@Retype.open_carg s env cs) T
    exact (hretype k st' m _).mpr hval

/-! ## Elimination forms -/

theorem sem_typ_tapp
  {x : BVar s .var}
  {S : Ty .shape s}
  {T : Ty .exi (s,X)}
  (hx : (.var (.bound x)) # Γ ⊨ .var (.bound x) : .typ (.capt (.var (.bound x)) (.poly S T))) :
  (.var (.bound x)) # Γ ⊨ Exp.tapp (.bound x) S : T.subst (Subst.openTVar S) := by
  intro env k st m hts hmt
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  obtain ⟨st1, hwle1, hmt1, hxval⟩ := ExpDenot.var_inv hkpos hmt (hx env k st m hts)
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at hxval
  obtain ⟨fx, hfx, cs, S0, e0, hval, R, hlk, hR0_sub, hfun⟩ := tabs_val_denot_inv hxval.2.2.2
  have : fx = env.lookup_var x := by cases hfx; rfl
  subst this
  have happ := hfun k (Nat.le_refl k) st1 m (Ty.shape_val_denot env S)
    (by rw [World.trunc_self]; exact WorldLe.refl _ _)
    (shape_val_denot_is_proper hts)
    (IPreDenot.ImplyAfter.refl _ _ _ _)
  have happ' := (ExpDenot.equiv (open_targ_exi_val_denot (env:=env) (S:=S) (T:=T))).mp happ
  have hrec := (ExpDenot.mono_auth hR0_sub happ') hmt1
  change Eval k _ m (Exp.tapp (.free (env.lookup_var x)) (S.subst (Subst.from_TypeEnv env))) _
  apply Eval.eval_tapply hlk
  refine eval_post_monotonic ?_ hrec
  intro t v m' _ hp hbud
  obtain ⟨st', hw, hmt', hd, hpb⟩ := hp hbud
  exact ⟨st', WorldLe.trans (WorldLe.trunc _ hwle1) hw, hmt', hd, hpb⟩

theorem sem_typ_capp
  {x : BVar s .var}
  {T : Ty .exi (s,C)}
  {D : CaptureSet s}
  (hD_closed : D.IsClosed)
  (hx : (.var (.bound x)) # Γ ⊨ .var (.bound x) :
    .typ (.capt (.var (.bound x)) (.cpoly (.bound D) T))) :
  (.var (.bound x)) # Γ ⊨ Exp.capp (.bound x) D : T.subst (Subst.openCVar D) := by
  intro env k st m hts hmt
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  obtain ⟨st1, hwle1, hmt1, hxval⟩ := ExpDenot.var_inv hkpos hmt (hx env k st m hts)
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at hxval
  obtain ⟨fx, hfx, cs, B0, e0, hval, R, hlk, hR0_sub, hfun⟩ := cabs_val_denot_inv hxval.2.2.2
  have : fx = env.lookup_var x := by cases hfx; rfl
  subst this
  let D' := D.subst (Subst.from_TypeEnv env)
  have hD'_denot : D'.denot TypeEnv.empty = D.denot env :=
    closed_captureset_subst_denot hD_closed
  have hD'_wf : D'.WfInHeap m.heap :=
    CaptureSet.wf_subst (CaptureSet.wf_of_closed hD_closed) (from_TypeEnv_wf_in_heap hts)
  have happ := hfun k (Nat.le_refl k) st1 m D' hD'_wf
    (by rw [World.trunc_self]; exact WorldLe.refl _ _)
    (by
      rw [hD'_denot]
      change (D.denot env m).BoundedBy (CapabilityBound.set (D.denot env m))
      exact CapabilitySet.BoundedBy.set CapabilitySet.Subset.refl)
  have happ' := (ExpDenot.equiv (open_carg_exi_val_denot (env:=env) (C:=D) (T:=T))).mp happ
  have hrec := (ExpDenot.mono_auth hR0_sub happ') hmt1
  change Eval k _ m (Exp.capp (.free (env.lookup_var x)) D') _
  apply Eval.eval_capply hlk
  refine eval_post_monotonic ?_ hrec
  intro t v m' _ hp hbud
  obtain ⟨st', hw, hmt', hd, hpb⟩ := hp hbud
  exact ⟨st', WorldLe.trans (WorldLe.trunc _ hwle1) hw, hmt', hd, hpb⟩

theorem sem_typ_app
  {x y : BVar s .var}
  (hx : (.var (.bound x)) # Γ ⊨ .var (.bound x) : .typ (.capt (.var (.bound x)) (.arrow T1 T2)))
  (hy : (.var (.bound y)) # Γ ⊨ .var (.bound y) : .typ T1) :
  ((.var (.bound x)) ∪ (.var (.bound y))) # Γ ⊨
    Exp.app (.bound x) (.bound y) : T2.subst (Subst.openVar (.bound y)) := by
  intro env k st m hts hmt
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  obtain ⟨stx, hwlex, hmtx, hxval⟩ := ExpDenot.var_inv hkpos hmt (hx env k st m hts)
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at hxval
  obtain ⟨fx, hfx, cs, T0, e0, hval, R, hlk, hR0_sub, hbody⟩ := abs_val_denot_inv hxval.2.2.2
  have : fx = env.lookup_var x := by cases hfx; rfl
  subst this
  have htsx := env_typing_worldle_down hts hwlex
  obtain ⟨sty, hwley, hmty, hyval⟩ := ExpDenot.var_inv hkpos hmtx (hy env k stx m htsx)
  simp only [Ty.exi_val_denot] at hyval
  have hbody' := hbody k (Nat.le_refl k) sty m (env.lookup_var y)
    (by rw [World.trunc_self]; exact hwley) hyval
  have hsub : expand_captures m.heap cs ∪ reachability_of_loc m.heap (env.lookup_var y) ⊆
      CaptureSet.denot env (CaptureSet.var (Var.bound x) ∪ CaptureSet.var (Var.bound y)) m :=
    CapabilitySet.union_mono_left hR0_sub
  have hrec := (ExpDenot.mono_auth hsub hbody') hmty
  change Eval k _ m (Exp.app (.free (env.lookup_var x)) (.free (env.lookup_var y))) _
  apply Eval.eval_apply hlk
  refine eval_post_monotonic ?_ hrec
  intro t v m' _ hp hbud
  obtain ⟨st', hw, hmt', hd, hpb⟩ := hp hbud
  refine ⟨st', WorldLe.trans (WorldLe.trunc _ (WorldLe.trans hwlex hwley)) hw, hmt', ?_, hpb⟩
  exact IDenot.equiv_ltr (open_arg_exi_val_denot (env:=env) (y:=.bound y) (T:=T2)) hd

theorem sem_typ_invoke
  {x y : BVar s .var}
  (hx : (.var (.bound x)) # Γ ⊨ .var (.bound x) : .typ (.capt (.var (.bound x)) .cap))
  (hy : (.var (.bound y)) # Γ ⊨ .var (.bound y) : .typ (.capt (.var (.bound y)) .unit)) :
  ((.var (.bound x)) ∪ (.var (.bound y))) # Γ ⊨
    Exp.app (.bound x) (.bound y) : .typ (.capt {} .unit) := by
  intro env k st m hts hmt
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  obtain ⟨stx, hwlex, hmtx, hxval⟩ := ExpDenot.var_inv hkpos hmt (hx env k st m hts)
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at hxval
  obtain ⟨fx, hfx, hlk_cap, hmem_cap⟩ := cap_val_denot_inv hxval.2.2.2
  obtain ⟨sty, hwley, hmty, hyval⟩ := ExpDenot.var_inv hkpos hmt (hy env k st m hts)
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at hyval
  obtain ⟨fy, hfy, hval_unit, R, hlk_unit⟩ := unit_val_denot_inv hyval.2.2.2
  have : fx = env.lookup_var x := by cases hfx; rfl
  subst this
  have : fy = env.lookup_var y := by cases hfy; rfl
  subst this
  have hmem :
    env.lookup_var x ∈ CaptureSet.denot env (.var (.bound x) ∪ .var (.bound y)) m :=
    .left hmem_cap
  change Eval k _ m (Exp.app (.free (env.lookup_var x)) (.free (env.lookup_var y))) _
  apply Eval.eval_invoke hmem hlk_cap hlk_unit
  exact ExpPost.access_intro st (WorldLe.refl _ _) hmt (unit_val_denot env k st m)
    (pack_bound_of_simple Exp.IsSimpleVal.unit)

theorem sem_typ_cond
  {C1 C2 C3 : CaptureSet s} {Γ : Ctx s}
  {x : Var .var s} {e2 e3 : Exp s} {T : Ty .exi s} {Cb : CaptureSet s}
  (ht1 : C1 # Γ ⊨ (.var x) : .typ (.capt Cb .bool))
  (ht2 : C2 # Γ ⊨ e2 : T)
  (ht3 : C3 # Γ ⊨ e3 : T) :
  (C1 ∪ C2 ∪ C3) # Γ ⊨ (.cond x e2 e3) : T := by
  intro env k st m hts hmt
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  obtain ⟨st1, hwle1, hmt1, hval1⟩ := ExpDenot.var_inv hkpos hmt (ht1 env k st m hts)
  simp only [Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot] at hval1
  have hres := hval1.2.2.2
  have hsubC2 : C2.denot env m ⊆ (C1 ∪ C2 ∪ C3).denot env m :=
    CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_right
      CapabilitySet.Subset.union_right_left
  have hsubC3 : C3.denot env m ⊆ (C1 ∪ C2 ∪ C3).denot env m :=
    CapabilitySet.Subset.union_right_right
  change Eval k _ m (.cond (x.subst (Subst.from_TypeEnv env))
    (e2.subst (Subst.from_TypeEnv env)) (e3.subst (Subst.from_TypeEnv env))) _
  refine Eval.eval_cond hres ?_ ?_
  · intro _
    exact (ExpDenot.mono_auth hsubC2 (ht2 env k st m hts)) hmt
  · intro _
    exact (ExpDenot.mono_auth hsubC3 (ht3 env k st m hts)) hmt


/-! ## Mutable cells -/

theorem sem_typ_alloc
  {x : BVar s .var} {T : Ty .capt s}
  (hx : (.var (.bound x)) # Γ ⊨ .var (.bound x) : .typ T) :
  {} # Γ ⊨ Exp.alloc (.bound x) :
    .exi (.capt (.cvar .here) (.cell (T.rename Rename.succ))) := by
  intro env k st m hts hmt
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  obtain ⟨st1, hwle1, hmt1, hval1⟩ := ExpDenot.var_inv hkpos hmt (hx env k st m hts)
  simp only [Ty.exi_val_denot] at hval1
  set fx := env.lookup_var x with hfx
  have hwf := capt_val_denot_implies_wf T hval1
  have hlk : m.heap fx ≠ none := by
    cases hwf with
    | wf_var hv => cases hv with | wf_free hh => exact Option.ne_none_iff_exists'.mpr ⟨_, hh⟩
  change Eval k _ m (Exp.alloc (.free fx)) _
  apply Eval.eval_alloc hlk
  intro l' hfresh
  -- The fresh cell stores the content type's denotation as a world-parametrized relation.
  set R : MonRel k := fun j w' m' e' => Ty.capt_val_denot env T j.val w' m' e' with hRdef
  have hsub_ext : (m.extend_mcell l' fx hfresh hlk).subsumes m :=
    Memory.extend_mcell_subsumes m l' fx hfresh hlk
  have hst1_fresh : st1.lookup l' = none := by
    rcases hopt : st1.lookup l' with _ | R0
    · rfl
    · obtain ⟨n, hlkn⟩ := hmt1.1 l' R0 hopt
      rw [show m.lookup l' = m.heap l' from rfl, hfresh] at hlkn
      cases hlkn
  have hRstable : ∀ (i : Fin k) (w1 w2 : StoreTyping i.val) (m1 m2 : Memory),
      WorldLe w2 m2 w1 m1 → ∀ e, R i w1 m1 e → R i w2 m2 e :=
    fun i _ _ _ _ hw e h => capt_val_denot_worldle_mono (typed_env_is_monotonic hts) T hw h
  have hwle_base : WorldLe (st1.set l' R) (m.extend_mcell l' fx hfresh hlk) st1 m := by
    refine ⟨hsub_ext, ?_⟩
    intro l R0 hl
    rw [World.set_lookup]
    by_cases hll' : l = l'
    · exfalso; subst hll'; rw [hst1_fresh] at hl; cases hl
    · rw [if_neg hll']; exact hl
  have hRext : ∀ (i : Fin k),
      R i ((st1.set l' R).trunc (Nat.le_of_lt i.isLt)) (m.extend_mcell l' fx hfresh hlk)
        (.var (.free fx)) := by
    intro i
    change Ty.capt_val_denot env T i.val ((st1.set l' R).trunc (Nat.le_of_lt i.isLt))
      (m.extend_mcell l' fx hfresh hlk) (.var (.free fx))
    have hdown := capt_val_denot_down_trunc (typed_env_is_downward_closed hts) T
      (Nat.le_of_lt i.isLt) hval1
    exact capt_val_denot_worldle_mono (typed_env_is_monotonic hts) T
      (WorldLe.trunc (Nat.le_of_lt i.isLt) hwle_base) hdown
  obtain ⟨walloc, hmtalloc⟩ := WT_alloc hfresh hlk hmt1 hRstable hRext
  have hlk_l' : (m.extend_mcell l' fx hfresh hlk).lookup l' = some (.capability (.mcell fx)) :=
    Memory.extend_mcell_lookup hfresh hlk
  have hlk_l'_heap : (m.extend_mcell l' fx hfresh hlk).heap l' =
      some (.capability (.mcell fx)) := hlk_l'
  apply ExpPost.alloc_intro (st1.set l' R) (WorldLe.trans hwle1 walloc) hmtalloc
  · simp only [Ty.exi_val_denot]
    refine ⟨.var (.free l'), .free l', rfl, CaptureSet.WfInHeap.wf_var_free hlk_l', ?_⟩
    simp only [Ty.capt_val_denot, Ty.shape_val_denot]
    refine ⟨.is_var, .wf_var (.wf_free hlk_l'), ?_, l', fx, R, rfl, hlk_l', ?_, ?_, ?_⟩
    · exact CaptureSet.WfInHeap.wf_var_free hlk_l'
    · change l' ∈ reachability_of_loc (m.extend_mcell l' fx hfresh hlk).heap l'
      rw [reachability_of_loc, hlk_l'_heap]
      exact CapabilitySet.mem.here
    · change (st1.set l' R).lookup l' = some R
      simp [World.set_lookup]
    · intro j w' m' e'
      exact cweaken_capt_val_denot (env := env) (cs := .var (.free l')) (T := T) j.val w' m' e'
  · intro cs0 fx0 heq
    injection heq with _ _ heq'
    injection heq' with _ _ heq'
    subst heq'
    rw [reachability_of_loc, hlk_l'_heap]
    exact CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left
      CapabilitySet.Subset.union_right_right

theorem sem_typ_read
  {x : BVar s .var} {C : CaptureSet s} {T : Ty .capt s}
  (hx : (.var (.bound x)) # Γ ⊨ .var (.bound x) : .typ (.capt C (.cell T))) :
  (.var (.bound x)) # Γ ⊨ Exp.read (.bound x) : .typ T := by
  intro env k st m hts hmt
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  obtain ⟨st1, hwle1, hmt1, hval1⟩ := ExpDenot.var_inv hkpos hmt (hx env k st m hts)
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at hval1
  obtain ⟨fx, n0, Rl, hfx, hlk_cell, _, hst, hbi⟩ := cell_val_denot_inv hval1.2.2.2
  have : fx = env.lookup_var x := by cases hfx; rfl
  subst this
  have hmem : env.lookup_var x ∈ (CaptureSet.var (Var.bound x)).denot env m := by
    change env.lookup_var x ∈ reachability_of_loc m.heap (env.lookup_var x)
    rw [reachability_of_loc, show m.heap (env.lookup_var x) = _ from hlk_cell]
    exact CapabilitySet.mem.here
  change Eval k _ m (Exp.read (.free (env.lookup_var x))) _
  apply Eval.eval_read hmem hlk_cell
  apply ExpPost.read_intro st1 hwle1 hmt1 ?_ pack_bound_of_var
  intro hpred
  simp only [Ty.exi_val_denot]
  exact (hbi ⟨k - 1, hpred⟩ (st1.trunc (Nat.sub_le k 1)) m (.var (.free n0))).mp
    (hmt1.2.2 _ n0 Rl hst hlk_cell ⟨k - 1, hpred⟩)

theorem sem_typ_write
  {x y : BVar s .var} {Cx : CaptureSet s} {T : Ty .capt s}
  (hx : (.var (.bound x)) # Γ ⊨ .var (.bound x) : .typ (.capt Cx (.cell T)))
  (hy : (.var (.bound y)) # Γ ⊨ .var (.bound y) : .typ T) :
  (.var (.bound x)) # Γ ⊨ Exp.write (.bound x) (.bound y) : .typ (.capt {} .unit) := by
  intro env k st m hts hmt
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  obtain ⟨st1, hwle1, hmt1, hval1⟩ := ExpDenot.var_inv hkpos hmt (hx env k st m hts)
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at hval1
  obtain ⟨fx, n0, Rl, hfx, hlk_cell, _, hst, hbi⟩ := cell_val_denot_inv hval1.2.2.2
  have : fx = env.lookup_var x := by cases hfx; rfl
  subst this
  -- Run `y`'s soundness at `x`'s post-world so that the cell is still typed `Rl` there.
  have hts1 : EnvTyping Γ env k st1 m := env_typing_worldle_down hts hwle1
  obtain ⟨st2, hwle2, hmt2, hval2⟩ := ExpDenot.var_inv hkpos hmt1 (hy env k st1 m hts1)
  simp only [Ty.exi_val_denot] at hval2
  have hst2 : st2.lookup (env.lookup_var x) = some Rl := hwle2.2 _ Rl hst
  have hwf_y := capt_val_denot_implies_wf T hval2
  have hly : m.heap (env.lookup_var y) ≠ none := by
    cases hwf_y with
    | wf_var hv => cases hv with | wf_free hh => exact Option.ne_none_iff_exists'.mpr ⟨_, hh⟩
  have hmem : env.lookup_var x ∈ (CaptureSet.var (Var.bound x)).denot env m := by
    change env.lookup_var x ∈ reachability_of_loc m.heap (env.lookup_var x)
    rw [reachability_of_loc, show m.heap (env.lookup_var x) = _ from hlk_cell]
    exact CapabilitySet.mem.here
  change Eval k _ m (Exp.write (.free (env.lookup_var x)) (.free (env.lookup_var y))) _
  apply Eval.eval_write hmem hlk_cell hly
  set m_upd := m.update_mcell (env.lookup_var x) (env.lookup_var y) ⟨n0, hlk_cell⟩ hly
    with hm_upd
  have hsub_upd : m_upd.subsumes m :=
    Memory.update_mcell_subsumes m (env.lookup_var x) (env.lookup_var y) ⟨n0, hlk_cell⟩ hly
  -- The written value satisfies the cell's stored relation at every lower level: the
  -- backward direction of the cell agreement.
  have hyR : ∀ (i : Fin k), Rl i (st2.trunc (Nat.le_of_lt i.isLt))
      m_upd (.var (.free (env.lookup_var y))) := by
    intro i
    refine (hbi i _ _ _).mpr ?_
    have hdown := capt_val_denot_down_trunc (typed_env_is_downward_closed hts) T
      (Nat.le_of_lt i.isLt) hval2
    exact capt_val_denot_worldle_mono (typed_env_is_monotonic hts) T
      (WorldLe.of_subsumes hsub_upd) hdown
  obtain ⟨hwle_w, hmt_w⟩ := WT_write hlk_cell hly hst2 hmt2 hyR
  exact ExpPost.access_intro st2 (WorldLe.trans (WorldLe.trans hwle1 hwle2) hwle_w) hmt_w
    (unit_val_denot env k st2 m_upd) (pack_bound_of_simple Exp.IsSimpleVal.unit)

/-! ## Sequencing -/

/-- The shared continuation runner of `sem_typ_letin`: given the freshly bound location
`l0` holding a `T`-value at the post-head world, run the continuation's semantic typing in
the extended environment and reassemble the outer postcondition. -/
theorem sem_typ_letin_cont
  {C : CaptureSet s} {Γ : Ctx s} {T : Ty .capt s} {e2 : Exp (s,x)} {U : Ty .exi s}
  {env : TypeEnv s} {k : Nat} {st : StoreTyping k} {m mb : Memory}
  {t1 : Trace} {st1 : StoreTyping (k - t1.readCount)} {l0 : Nat}
  (hclosed_C : C.IsClosed)
  (ht2 : C.rename Rename.succ # (Γ,x:T) ⊨ e2 : U.rename Rename.succ)
  (hts : EnvTyping Γ env k st m)
  (hwle1 : WorldLe st1 mb (st.trunc (Nat.sub_le k t1.readCount)) m)
  (hmt1 : MemTyped (k - t1.readCount) st1 mb)
  (hval : Ty.capt_val_denot env T (k - t1.readCount) st1 mb (.var (.free l0))) :
  Eval (k - t1.readCount) (C.denot env m ∪ CapabilitySet.ofList t1.allocList) mb
    ((e2.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free l0)))
    (fun t2 => ExpPost k st m (C.denot env m) (Ty.exi_val_denot env U) (t1 ++ t2)) := by
  have hts_mb : EnvTyping Γ env (k - t1.readCount) st1 mb :=
    env_typing_worldle_trunc (Nat.sub_le k t1.readCount) hts hwle1
  have henv2 : EnvTyping (Γ,x:T) (env.extend_var l0) (k - t1.readCount) st1 mb :=
    ⟨hval, hts_mb⟩
  have he2 := ht2 (env.extend_var l0) (k - t1.readCount) st1 mb henv2 hmt1
  have hkey := @Exp.from_TypeEnv_weaken_open s env l0 e2
  refine hkey ▸ ?_
  have hR2 : (C.rename Rename.succ).denot (env.extend_var l0) mb = C.denot env m := by
    have h1 : (C.rename Rename.succ).denot (env.extend_var l0) = C.denot env :=
      (rebind_captureset_denot (Rebind.weaken (env := env) (x := l0)) C).symm
    rw [congrFun h1 mb]
    exact (closed_capture_denot_monotonic hclosed_C hts hwle1.1).symm
  have he2' : Eval (k - t1.readCount) (C.denot env m) mb
      (e2.subst (Subst.from_TypeEnv (env.extend_var l0)))
      (ExpPost (k - t1.readCount) st1 mb (C.denot env m)
        (Ty.exi_val_denot (env.extend_var l0) (U.rename Rename.succ))) := by
    rw [← hR2]; exact he2
  refine eval_post_monotonic ?_ (Eval.mono_auth CapabilitySet.Subset.union_right_left he2')
  intro t2 v m' _ hp hguard
  have hbud2 : t2.readCount < k - t1.readCount := by
    rw [Trace.readCount_append] at hguard; omega
  obtain ⟨st', hwle2, hmt2, hval2, hpb2⟩ := hp hbud2
  have hidx_eq : k - (t1 ++ t2).readCount = (k - t1.readCount) - t2.readCount := by
    rw [Trace.readCount_append, Nat.sub_sub]
  have hjk : k - (t1 ++ t2).readCount ≤ (k - t1.readCount) - t2.readCount :=
    Nat.le_of_eq hidx_eq
  have h2le : (k - t1.readCount) - t2.readCount ≤ k - t1.readCount := Nat.sub_le _ _
  refine ⟨st'.trunc hjk, ?_, MemTyped_trunc hjk hmt2, ?_, ?_⟩
  · have hwle1_desc := WorldLe.trunc h2le hwle1
    rw [World.trunc_trunc] at hwle1_desc
    have hwle_comp := WorldLe.trans hwle1_desc hwle2
    have hwle_fin := WorldLe.trunc hjk hwle_comp
    rw [World.trunc_trunc] at hwle_fin
    exact hwle_fin
  · have hval_env : Ty.exi_val_denot env U ((k - t1.readCount) - t2.readCount) st' m' v :=
      IDenot.equiv_rtl (weaken_exi_val_denot (env := env) (T := U) (x := l0)) hval2
    exact exi_val_denot_down_trunc (typed_env_is_downward_closed hts) U hjk hval_env
  · exact pack_bound_append (pack_bound_mono CapabilitySet.Subset.union_right_left hpb2)

theorem sem_typ_letin
  {C : CaptureSet s} {Γ : Ctx s} {e1 : Exp s} {T : Ty .capt s}
  {e2 : Exp (s,,Kind.var)} {U : Ty .exi s}
  (hclosed_C : C.IsClosed)
  (ht1 : C # Γ ⊨ e1 : T.typ)
  (ht2 : C.rename Rename.succ # (Γ,x:T) ⊨ e2 : U.rename Rename.succ) :
  C # Γ ⊨ (Exp.letin e1 e2) : U := by
  intro env k st m hts hmt
  have he1 := ht1 env k st m hts hmt
  change Eval k _ m (Exp.letin (e1.subst (Subst.from_TypeEnv env))
    (e2.subst (Subst.from_TypeEnv env).lift)) _
  refine Eval.eval_letin he1 (fun _ _ _ hover hguard => absurd hguard (Nat.not_lt.mpr hover))
    ?_ ?_ ?_
  · intro t1 m1 v hbud hq1
    obtain ⟨st1, _, _, hval1, _⟩ := hq1 hbud
    simp only [Ty.exi_val_denot] at hval1
    exact ⟨capt_val_denot_implies_simple_ans T hval1, capt_val_denot_implies_wf T hval1⟩
  · intro t1 m1 v hbud _ hv hwf_v hq1 l' hfresh
    obtain ⟨st1, hwle1, hmt1, hval1, _⟩ := hq1 hbud
    simp only [Ty.exi_val_denot] at hval1
    set w : HeapVal := ⟨v, hv, compute_reachability m1.heap v hv⟩ with hw
    set m_ext := m1.extend_val l' w hwf_v rfl hfresh with hm_ext
    have hsub_ext : m_ext.subsumes m1 := Memory.extend_val_subsumes m1 l' w hwf_v rfl hfresh
    have hmt_ext : MemTyped (k - t1.readCount) st1 m_ext :=
      WT_extend_val hwf_v rfl hfresh hmt1
    have hlookup_l' : m_ext.lookup l' = some (.val w) := by
      rw [hm_ext]; simp [Memory.lookup, Memory.extend_val, Heap.extend]
    have hval_var : Ty.capt_val_denot env T (k - t1.readCount) st1 m_ext (.var (.free l')) :=
      capt_val_denot_is_transparent (typed_env_is_transparent hts) T _ _ hlookup_l'
        (capt_val_denot_is_monotonic (typed_env_is_monotonic hts) T _ _ hsub_ext hval1)
    have hwle1_ext : WorldLe st1 m_ext (st.trunc (Nat.sub_le k t1.readCount)) m :=
      ⟨Memory.subsumes_trans hsub_ext hwle1.1, hwle1.2⟩
    exact sem_typ_letin_cont hclosed_C ht2 hts hwle1_ext hmt_ext hval_var
  · intro t1 m1 x0 hbud _ _ hq1
    obtain ⟨st1, hwle1, hmt1, hval1, _⟩ := hq1 hbud
    simp only [Ty.exi_val_denot] at hval1
    cases x0 with
    | bound b => cases b
    | free fx0 =>
      exact sem_typ_letin_cont hclosed_C ht2 hts hwle1 hmt1 hval1

lemma simple_val_not_pack {e : Exp s}
  (hsimple : e.IsSimpleVal)
  (hpack : e.IsPack) : False := by
  cases hsimple <;> cases hpack

lemma resolve_pack_eq {e : Exp {}} {m : Memory} {CS : CaptureSet {}} {x : Var .var {}}
  (hres : resolve m.heap e = some (.pack CS x))
  (hpack : e.IsPack) : e = .pack CS x := by
  cases hpack
  rename_i cs y
  change some (Exp.pack cs y) = some (Exp.pack CS x) at hres
  cases hres
  rfl

theorem resolve_is_pack {e : Exp {}} {m : Memory}
  (hres : resolve m.heap e = some v)
  (hv : v.IsPack) : e.IsPack := by
  cases (resolve_var_or_val (store := m.heap) (e := e) (v := v) hres) with
  | inr heq =>
    rw [heq]
    exact hv
  | inl hvar =>
    obtain ⟨x, rfl⟩ := hvar
    cases x with
    | bound bv => cases bv
    | free fy =>
      cases hval : m.heap fy with
      | none =>
        simp only [resolve, hval] at hres
        contradiction
      | some cell =>
        cases cell with
        | val val =>
          simp only [resolve, hval] at hres
          cases hres
          exfalso
          exact simple_val_not_pack val.isVal hv
        | capability info =>
          simp only [resolve, hval] at hres
          contradiction
        | masked =>
          simp only [resolve, hval] at hres
          contradiction

theorem sem_typ_unpack
    {C : CaptureSet s} {Γ : Ctx s} {t : Exp s} {T : Ty .capt (s,C)}
    {u : Exp (s,C,x)} {U : Ty .exi s}
    (hclosed_C : C.IsClosed)
    (ht : C # Γ ⊨ t : .exi T)
    (hu : ((C.rename Rename.succ).rename Rename.succ ∪ (.var (.bound .here))) #
          (Γ,C<:.unbound,x:T) ⊨ u : (U.rename Rename.succ).rename Rename.succ) :
    C # Γ ⊨ (Exp.unpack t u) : U := by
  intro env k st m hts hmt
  have he1 := ht env k st m hts hmt
  change Eval k _ m (Exp.unpack (t.subst (Subst.from_TypeEnv env))
    (u.subst (Subst.from_TypeEnv env).lift.lift)) _
  refine Eval.eval_unpack he1 (fun _ _ _ hover hguard => absurd hguard (Nat.not_lt.mpr hover))
    ?_ ?_
  · intro t1 m1 v hbud hq1
    obtain ⟨st1, _, _, hval1, _⟩ := hq1 hbud
    simp only [Ty.exi_val_denot] at hval1
    obtain ⟨CS, y, hres, hwf_CS, hbody⟩ := hval1
    have hpack : v.IsPack := resolve_is_pack hres Exp.IsPack.pack
    have heq := resolve_pack_eq hres hpack
    subst heq
    refine ⟨Exp.IsPack.pack, Exp.WfInHeap.wf_pack hwf_CS ?_⟩
    cases capt_val_denot_implies_wf T hbody with
    | wf_var h => exact h
  · intro t1 m1 x0 cs hbud _ _ hwf_cs hq1
    obtain ⟨st1, hwle1, hmt1, hval1, hpb1⟩ := hq1 hbud
    simp only [Ty.exi_val_denot] at hval1
    obtain ⟨CS, y, hres, _, hbody⟩ := hval1
    have hres' : Exp.pack cs x0 = Exp.pack CS y := Option.some.inj hres
    injection hres' with _ h1 h2
    subst h1; subst h2
    cases x0 with
    | bound b => cases b
    | free fx =>
      have hfx_bound := hpb1 cs fx rfl
      have hts_m1 : EnvTyping Γ env (k - t1.readCount) st1 m1 :=
        env_typing_worldle_trunc (Nat.sub_le k t1.readCount) hts hwle1
      have henv2 : EnvTyping (Γ,C<:.unbound,x:T) ((env.extend_cvar cs).extend_var fx)
          (k - t1.readCount) st1 m1 := by
        refine ⟨hbody, hwf_cs, ?_, ?_, hts_m1⟩
        · simpa only [List.empty_eq] using CaptureBound.WfInHeap.wf_unbound
        · simpa only [List.empty_eq] using CapabilitySet.BoundedBy.top
      have hu' := hu ((env.extend_cvar cs).extend_var fx) (k - t1.readCount) st1 m1 henv2 hmt1
      have hexp_eq :
          (u.subst (Subst.from_TypeEnv env).lift.lift).subst (Subst.unpack cs (Var.free fx)) =
          u.subst (Subst.from_TypeEnv ((env.extend_cvar cs).extend_var fx)) := by
        rw [Exp.subst_comp]
        exact congrArg _ Subst.from_TypeEnv_weaken_unpack
      change Eval _ _ m1
        ((u.subst (Subst.from_TypeEnv env).lift.lift).subst (Subst.unpack cs (Var.free fx))) _
      rw [hexp_eq]
      have hcap_C_eq :
          ((C.rename Rename.succ).rename Rename.succ).denot
            ((env.extend_cvar cs).extend_var fx) m1 = C.denot env m := by
        have h1 := rebind_captureset_denot (Rebind.cweaken (env:=env) (cs:=cs)) C
        have h2 := rebind_captureset_denot
          (Rebind.weaken (env:=env.extend_cvar cs) (x:=fx)) (C.rename Rename.succ)
        calc
          ((C.rename Rename.succ).rename Rename.succ).denot
            ((env.extend_cvar cs).extend_var fx) m1
          _ = (C.rename Rename.succ).denot (env.extend_cvar cs) m1 := congrFun h2.symm m1
          _ = C.denot env m1 := congrFun h1.symm m1
          _ = C.denot env m := (closed_capture_denot_monotonic hclosed_C hts hwle1.1).symm
      have hcap_var_eq :
          (CaptureSet.var (.bound .here : Var .var (s,C,x))).denot
            ((env.extend_cvar cs).extend_var fx) m1 = reachability_of_loc m1.heap fx := by
        simp [CaptureSet.denot, CaptureSet.ground_denot, CaptureSet.subst,
              Var.subst, Subst.from_TypeEnv, TypeEnv.lookup_var, TypeEnv.extend_var]
        rfl
      have hcap_sub :
          ((C.rename Rename.succ).rename Rename.succ ∪ (.var (.bound .here))).denot
            ((env.extend_cvar cs).extend_var fx) m1 ⊆
            C.denot env m ∪ CapabilitySet.ofList t1.allocList := by
        change ((C.rename Rename.succ).rename Rename.succ).denot
            ((env.extend_cvar cs).extend_var fx) m1
          ∪ (CaptureSet.var (.bound .here : Var .var (s,C,x))).denot
            ((env.extend_cvar cs).extend_var fx) m1
          ⊆ C.denot env m ∪ CapabilitySet.ofList t1.allocList
        rw [hcap_C_eq, hcap_var_eq]
        exact CapabilitySet.Subset.union_left CapabilitySet.Subset.union_right_left hfx_bound
      refine eval_post_monotonic ?_ (Eval.mono_auth hcap_sub hu')
      intro t2 v m' _ hp hguard
      have hbud2 : t2.readCount < k - t1.readCount := by
        rw [Trace.readCount_append] at hguard; omega
      obtain ⟨st', hwle2, hmt2, hval2, hpb2⟩ := hp hbud2
      have hidx_eq : k - (t1 ++ t2).readCount = (k - t1.readCount) - t2.readCount := by
        rw [Trace.readCount_append, Nat.sub_sub]
      have hjk : k - (t1 ++ t2).readCount ≤ (k - t1.readCount) - t2.readCount :=
        Nat.le_of_eq hidx_eq
      have h2le : (k - t1.readCount) - t2.readCount ≤ k - t1.readCount := Nat.sub_le _ _
      refine ⟨st'.trunc hjk, ?_, MemTyped_trunc hjk hmt2, ?_, ?_⟩
      · have hwle1_desc := WorldLe.trunc h2le hwle1
        rw [World.trunc_trunc] at hwle1_desc
        have hwle_comp := WorldLe.trans hwle1_desc hwle2
        have hwle_fin := WorldLe.trunc hjk hwle_comp
        rw [World.trunc_trunc] at hwle_fin
        exact hwle_fin
      · have hval_env : Ty.exi_val_denot env U ((k - t1.readCount) - t2.readCount) st' m' v :=
          IDenot.equiv_rtl (cweaken_exi_val_denot (env:=env) (cs:=cs) (T:=U))
            (IDenot.equiv_rtl (weaken_exi_val_denot (env:=env.extend_cvar cs)
              (T:=U.rename Rename.succ) (x:=fx)) hval2)
        exact exi_val_denot_down_trunc (typed_env_is_downward_closed hts) U hjk hval_env
      · exact pack_bound_append (pack_bound_mono hcap_sub hpb2)


/-! ## Subcapturing -/

theorem sem_sc_trans
  (hsub1 : SemSubcapt Γ C1 C2)
  (hsub2 : SemSubcapt Γ C2 C3) :
  SemSubcapt Γ C1 C3 := by
  intro env k st m hts
  exact CapabilitySet.Subset.trans (hsub1 env k st m hts) (hsub2 env k st m hts)

theorem sem_sc_elem {C1 C2 : CaptureSet s}
  (hmem : C1 ⊆ C2) :
  SemSubcapt Γ C1 C2 := by
  intro env k st m hts
  unfold CaptureSet.denot
  induction hmem
  case refl =>
    exact CapabilitySet.Subset.refl
  case union_left ih1 ih2 =>
    simpa only [List.empty_eq] using CapabilitySet.Subset.union_left ih1 ih2
  case union_right_left ih =>
    simpa only [List.empty_eq] using
      CapabilitySet.Subset.trans ih CapabilitySet.Subset.union_right_left
  case union_right_right ih =>
    simpa only [List.empty_eq] using
      CapabilitySet.Subset.trans ih CapabilitySet.Subset.union_right_right

theorem sem_sc_union {C1 C2 C3 : CaptureSet s}
  (hsub1 : SemSubcapt Γ C1 C3)
  (hsub2 : SemSubcapt Γ C2 C3) :
  SemSubcapt Γ (C1.union C2) C3 := by
  intro env k st m hts
  unfold CaptureSet.denot
  simpa only [List.empty_eq] using
    CapabilitySet.Subset.union_left (hsub1 env k st m hts) (hsub2 env k st m hts)

theorem typed_env_lookup_cvar_aux
  (hts : EnvTyping Γ env k st m)
  (hc : Ctx.LookupCVar Γ c cb) :
  ((env.lookup_cvar c).ground_denot m).BoundedBy ((cb.denot env) m) := by
  induction hc generalizing m
  case here =>
    rename_i Γ' cb'
    cases env; rename_i info' env'
    cases info'; rename_i cs
    unfold EnvTyping at hts
    change
      (cs.ground_denot m).BoundedBy
        ((cb'.rename Rename.succ).denot (env'.extend (TypeInfo.cvar cs)) m)
    have hreb := rebind_capturebound_denot (Rebind.cweaken (env:=env') (cs:=cs)) cb'
    simp only [TypeEnv.extend_cvar] at hreb
    rw [<-hreb]
    exact hts.2.2.1
  case there b0 b hc_prev ih =>
    cases b0
    case var =>
      rename_i Γ' c' cb' Tb
      cases env; rename_i info' env'
      cases info'; rename_i x
      unfold EnvTyping at hts
      obtain ⟨_, henv'⟩ := hts
      have hih := ih henv'
      change
        ((env'.lookup_cvar c').ground_denot m).BoundedBy
          ((cb'.rename Rename.succ).denot (env'.extend (TypeInfo.var x)) m)
      have hreb := rebind_capturebound_denot (Rebind.weaken (env:=env') (x:=x)) cb'
      simp only [TypeEnv.extend_var] at hreb
      rw [<-hreb]
      exact hih
    case tvar =>
      rename_i Γ' c' cb' Sb
      cases env; rename_i info' env'
      cases info'; rename_i d
      unfold EnvTyping at hts
      obtain ⟨_, _, henv'⟩ := hts
      have hih := ih henv'
      change
        ((env'.lookup_cvar c').ground_denot m).BoundedBy
          ((cb'.rename Rename.succ).denot (env'.extend (TypeInfo.tvar d)) m)
      have hreb := rebind_capturebound_denot (Rebind.tweaken (env:=env') (d:=d)) cb'
      simp only [TypeEnv.extend_tvar] at hreb
      rw [<-hreb]
      exact hih
    case cvar =>
      rename_i Γ' c' cb' Bb
      cases env; rename_i info' env'
      cases info'; rename_i cs
      unfold EnvTyping at hts
      obtain ⟨_, _, _, henv'⟩ := hts
      have hih := ih henv'
      change
        ((env'.lookup_cvar c').ground_denot m).BoundedBy
          ((cb'.rename Rename.succ).denot (env'.extend (TypeInfo.cvar cs)) m)
      have hreb := rebind_capturebound_denot (Rebind.cweaken (env:=env') (cs:=cs)) cb'
      simp only [TypeEnv.extend_cvar] at hreb
      rw [<-hreb]
      exact hih

theorem typed_env_lookup_cvar
  (hts : EnvTyping Γ env k st m)
  (hc : Ctx.LookupCVar Γ c (.bound C)) :
  (env.lookup_cvar c).ground_denot m ⊆ C.denot env m := by
  have h := typed_env_lookup_cvar_aux hts hc
  change
    ((env.lookup_cvar c).ground_denot m).BoundedBy
      (CapabilityBound.set (C.denot env m)) at h
  cases h with
  | set hsub => exact hsub

theorem sem_sc_var {x : BVar s .var} {C : CaptureSet s} {S : Ty .shape s}
  (hlookup : Γ.LookupVar x (.capt C S)) :
  SemSubcapt Γ (.var (.bound x)) C := by
  intro env k st m hts
  change reachability_of_loc m.heap (env.lookup_var x) ⊆ C.denot env m
  simpa [Ty.captureSet] using typed_env_lookup_var_reachability hts hlookup

theorem sem_sc_cvar {c : BVar s .cvar} {C : CaptureSet s}
  (hlookup : Γ.LookupCVar c (.bound C)) :
  SemSubcapt Γ (.cvar c) C := by
  intro env k st m hts
  change (env.lookup_cvar c).ground_denot m ⊆ C.denot env m
  exact typed_env_lookup_cvar hts hlookup

theorem fundamental_subcapt
  (hsub : Subcapt Γ C1 C2) :
  SemSubcapt Γ C1 C2 := by
  induction hsub
  case sc_trans => grind [sem_sc_trans]
  case sc_elem hsub => exact sem_sc_elem hsub
  case sc_union ih1 ih2 => exact sem_sc_union ih1 ih2
  case sc_cvar hlookup => exact sem_sc_cvar hlookup
  case sc_var hlookup => exact sem_sc_var hlookup

/-! ## Subtyping -/

/-- Lift a base world step and an index drop to a world step from the truncated base. -/
theorem WorldLe.trunc_step {k j i : Nat} (hjk : j ≤ k) (hij : i ≤ j)
    {st : StoreTyping k} {st' : StoreTyping j} {st'' : StoreTyping i} {m m' m'' : Memory}
    (hwle : WorldLe st' m' (st.trunc hjk) m) (hwle' : WorldLe st'' m'' (st'.trunc hij) m') :
    WorldLe st'' m'' (st.trunc (Nat.le_trans hij hjk)) m := by
  have h := WorldLe.trunc hij hwle
  rw [World.trunc_trunc] at h
  exact WorldLe.trans h hwle'

lemma sem_subtyp_top {T : Ty .shape s} :
  SemSubtyp Γ T .top := by
  intro env k st m hts R j hjk st' m' hwle e hd
  simp only [Ty.shape_val_denot]
  exact ⟨shape_val_denot_implies_wf (typed_env_is_implying_wf hts) T R j st' m' e hd,
    shape_val_denot_is_reachability_safe (typed_env_is_reachability_safe hts) T R j st' m' e hd⟩

lemma env_typing_lookup_tvar {X : BVar s .tvar} {S : Ty .shape s} {env : TypeEnv s}
  {k : Nat} {st : StoreTyping k} {m : Memory}
  (hlookup : Ctx.LookupTVar Γ X S)
  (htyping : EnvTyping Γ env k st m) :
  (env.lookup_tvar X).ImplyAfter k st m (Ty.shape_val_denot env S) := by
  induction hlookup generalizing m
  case here Γ S =>
    cases env; rename_i info0 env0
    cases info0; rename_i d
    unfold EnvTyping at htyping
    obtain ⟨hproper, himply, htyping'⟩ := htyping
    simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]
    have hw : Ty.shape_val_denot env0 S ≈
        Ty.shape_val_denot (env0.extend_tvar d) (S.rename Rename.succ) :=
      tweaken_shape_val_denot (env := env0) (d := d) (T := S)
    exact IPreDenot.ImplyAfter.trans himply
      (fun C => IDenot.equiv_to_imply_after (hw C) k st m)
  case there Γ X S b a a_ih =>
    cases b with
    | var T =>
      cases env; rename_i info env0
      cases info; rename_i v
      unfold EnvTyping at htyping
      obtain ⟨_, htyping'⟩ := htyping
      simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]
      have ih_result : (env0.lookup_tvar X).ImplyAfter k st m (Ty.shape_val_denot env0 S) := by
        simpa only [TypeEnv.lookup_tvar] using a_ih htyping'
      have hw : Ty.shape_val_denot env0 S ≈
          Ty.shape_val_denot (env0.extend_var v) (S.rename Rename.succ) :=
        weaken_shape_val_denot (env := env0) (x := v) (T := S)
      exact IPreDenot.ImplyAfter.trans ih_result
        (fun C => IDenot.equiv_to_imply_after (hw C) k st m)
    | tvar T =>
      cases env; rename_i info env0
      cases info; rename_i d
      unfold EnvTyping at htyping
      obtain ⟨_, _, htyping'⟩ := htyping
      simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]
      have ih_result : (env0.lookup_tvar X).ImplyAfter k st m (Ty.shape_val_denot env0 S) := by
        simpa only [TypeEnv.lookup_tvar] using a_ih htyping'
      have hw : Ty.shape_val_denot env0 S ≈
          Ty.shape_val_denot (env0.extend_tvar d) (S.rename Rename.succ) :=
        tweaken_shape_val_denot (env := env0) (d := d) (T := S)
      exact IPreDenot.ImplyAfter.trans ih_result
        (fun C => IDenot.equiv_to_imply_after (hw C) k st m)
    | cvar cb =>
      cases env; rename_i info env0
      cases info; rename_i cs
      unfold EnvTyping at htyping
      obtain ⟨_, _, _, htyping'⟩ := htyping
      simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]
      have ih_result : (env0.lookup_tvar X).ImplyAfter k st m (Ty.shape_val_denot env0 S) := by
        simpa only [TypeEnv.lookup_tvar] using a_ih htyping'
      have hw : Ty.shape_val_denot env0 S ≈
          Ty.shape_val_denot (env0.extend_cvar cs) (S.rename Rename.succ) :=
        cweaken_shape_val_denot (env := env0) (cs := cs) (T := S)
      exact IPreDenot.ImplyAfter.trans ih_result
        (fun C => IDenot.equiv_to_imply_after (hw C) k st m)

lemma sem_subtyp_tvar {X : BVar s .tvar} {S : Ty .shape s}
  (hlookup : Ctx.LookupTVar Γ X S) :
  SemSubtyp Γ (.tvar X) S := by
  intro env k st m htyping
  simpa only [Ty.shape_val_denot] using env_typing_lookup_tvar hlookup htyping

lemma sem_subtyp_arrow {T1 T2 : Ty .capt s} {U1 U2 : Ty .exi (s,x)}
  (harg : SemSubtyp Γ T2 T1)
  (hres : SemSubtyp (Γ,x:T2) U1 U2) :
  SemSubtyp Γ (.arrow T1 U1) (.arrow T2 U2) := by
  intro env k st m hts A j hjk st' m' hwle e h
  simp only [Ty.shape_val_denot] at h ⊢
  obtain ⟨hwf, cs, T0, t0, hresolve, hcs_wf, hR0_subset, hbody⟩ := h
  refine ⟨hwf, cs, T0, t0, hresolve, hcs_wf, hR0_subset, ?_⟩
  intro i hij st'' m'' arg hwle'' harg_T2
  have hwle_base := WorldLe.trunc_step hjk hij hwle hwle''
  have harg_T1 : Ty.capt_val_denot env T1 i st'' m'' (.var (.free arg)) :=
    harg env k st m hts i (Nat.le_trans hij hjk) st'' m'' hwle_base _ harg_T2
  have hb := hbody i hij st'' m'' arg hwle'' harg_T1
  have hts_ext : EnvTyping (Γ,x:T2) (env.extend_var arg) i st'' m'' :=
    ⟨harg_T2, env_typing_worldle_trunc _ hts hwle_base⟩
  exact ExpDenot.imply_after (hres (env.extend_var arg) i st'' m'' hts_ext) hb

lemma sem_subtyp_trans {sort : TySort} {T1 T2 T3 : Ty sort s}
  (h12 : SemSubtyp Γ T1 T2)
  (h23 : SemSubtyp Γ T2 T3) :
  SemSubtyp Γ T1 T3 := by
  cases sort with
  | shape =>
    intro env k st m htyping
    exact IPreDenot.ImplyAfter.trans (h12 env k st m htyping) (h23 env k st m htyping)
  | capt =>
    intro env k st m htyping
    exact IDenot.ImplyAfter.trans (h12 env k st m htyping) (h23 env k st m htyping)
  | exi =>
    intro env k st m htyping
    exact IDenot.ImplyAfter.trans (h12 env k st m htyping) (h23 env k st m htyping)

lemma sem_subtyp_refl {sort : TySort} {T : Ty sort s} :
  SemSubtyp Γ T T := by
  cases sort with
  | shape =>
    intro env k st m _
    exact IPreDenot.ImplyAfter.refl _ k st m
  | capt =>
    intro env k st m _
    exact IDenot.ImplyAfter.refl _ k st m
  | exi =>
    intro env k st m _
    exact IDenot.ImplyAfter.refl _ k st m

def SemSubbound (Γ : Ctx s) (B1 B2 : CaptureBound s) : Prop :=
  ∀ env k st m,
    EnvTyping Γ env k st m ->
    B1.denot env m ⊆ B2.denot env m

lemma fundamental_subbound
  (hsub : Subbound Γ B1 B2) :
  SemSubbound Γ B1 B2 := by
  induction hsub with
  | capset hsubcapt =>
    intro env k st m htyping
    have hsem := fundamental_subcapt hsubcapt
    simpa [CaptureBound.denot] using CapabilityBound.SubsetEq.set (hsem env k st m htyping)
  | top =>
    intro env k st m htyping
    change CapabilityBound.SubsetEq _ CapabilityBound.top
    exact CapabilityBound.SubsetEq.top

lemma sem_subtyp_cpoly {cb1 cb2 : CaptureBound s} {T1 T2 : Ty .exi (s,C)}
  (hB : SemSubbound Γ cb1 cb2)
  (hT : SemSubtyp (Γ,C<:cb1) T1 T2)
  (hclosed_cb1 : cb1.IsClosed) :
  SemSubtyp Γ (.cpoly cb2 T1) (.cpoly cb1 T2) := by
  intro env k st m hts A j hjk st' m' hwle e h
  simp only [Ty.shape_val_denot] at h ⊢
  obtain ⟨hwf, cs, B0, t0, hresolve, hcs_wf, hR0_subset, hbody⟩ := h
  refine ⟨hwf, cs, B0, t0, hresolve, hcs_wf, hR0_subset, ?_⟩
  intro i hij st'' m'' CS hCS_wf hwle'' hbound1
  have hwle_base := WorldLe.trunc_step hjk hij hwle hwle''
  have hts_m'' : EnvTyping Γ env i st'' m'' := env_typing_worldle_trunc _ hts hwle_base
  have hbound2 : (CS.denot TypeEnv.empty m'').BoundedBy (cb2.denot env m'') :=
    CapabilitySet.BoundedBy.trans hbound1 (hB env i st'' m'' hts_m'')
  have hb := hbody i hij st'' m'' CS hCS_wf hwle'' hbound2
  have henv' : EnvTyping (Γ,C<:cb1) (env.extend_cvar CS) i st'' m'' := by
    refine ⟨hCS_wf, ?_, ?_, hts_m''⟩
    · exact CaptureBound.wf_subst (CaptureBound.wf_of_closed hclosed_cb1)
        (from_TypeEnv_wf_in_heap hts_m'')
    · have heq : CS.denot TypeEnv.empty = CS.ground_denot := by
        funext mm
        simp [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id]
      rw [← heq]
      exact hbound1
  exact ExpDenot.imply_after (hT (env.extend_cvar CS) i st'' m'' henv') hb

lemma sem_subtyp_capt {C1 C2 : CaptureSet s} {S1 S2 : Ty .shape s}
  (hC : SemSubcapt Γ C1 C2)
  (hS : SemSubtyp Γ S1 S2)
  (hclosed_C2 : C2.IsClosed) :
  SemSubtyp Γ (.capt C1 S1) (.capt C2 S2) := by
  intro env k st m hts j hjk st' m' hwle e h
  simp only [Ty.capt_val_denot] at h ⊢
  obtain ⟨hsimple, hwf, hC1_wf, hS1⟩ := h
  have hts' : EnvTyping Γ env j st' m' := env_typing_worldle_trunc hjk hts hwle
  refine ⟨hsimple, hwf,
    CaptureSet.wf_subst (CaptureSet.wf_of_closed hclosed_C2) (from_TypeEnv_wf_in_heap hts'), ?_⟩
  have hsub := hC env j st' m' hts'
  have hS1' := shape_val_denot_is_reachability_monotonic
    (typed_env_is_reachability_monotonic hts) S1 _ _ hsub j st' m' e hS1
  exact hS env k st m hts (C2.denot env m') j hjk st' m' hwle e hS1'

lemma sem_subtyp_exi {T1 T2 : Ty .capt (s,C)}
  (hT : SemSubtyp (Γ,C<:.unbound) T1 T2) :
  SemSubtyp Γ (.exi T1) (.exi T2) := by
  intro env k st m hts j hjk st' m' hwle e h
  simp only [Ty.exi_val_denot] at h ⊢
  obtain ⟨CS, y, hres, hwf_CS, hbody⟩ := h
  have henv' : EnvTyping (Γ,C<:.unbound) (env.extend_cvar CS) j st' m' := by
    refine ⟨hwf_CS, ?_, ?_, env_typing_worldle_trunc hjk hts hwle⟩
    · simpa only [List.empty_eq] using CaptureBound.WfInHeap.wf_unbound
    · simpa only [List.empty_eq] using CapabilitySet.BoundedBy.top
  exact ⟨CS, y, hres, hwf_CS,
    IDenot.imply_after_apply (hT (env.extend_cvar CS) j st' m' henv') hbody⟩

lemma sem_subtyp_typ {T1 T2 : Ty .capt s}
  (hT : SemSubtyp Γ T1 T2) :
  SemSubtyp Γ (.typ T1) (.typ T2) := by
  intro env k st m htyping
  simpa only [Ty.exi_val_denot] using hT env k st m htyping

lemma sem_subtyp_poly {S1 S2 : Ty .shape s} {T1 T2 : Ty .exi (s,X)}
  (hS : SemSubtyp Γ S2 S1)
  (hT : SemSubtyp (Γ,X<:S2) T1 T2) :
  SemSubtyp Γ (.poly S1 T1) (.poly S2 T2) := by
  intro env k st m hts A j hjk st' m' hwle e h
  simp only [Ty.shape_val_denot] at h ⊢
  obtain ⟨hwf, cs, S0, t0, hresolve, hcs_wf, hR0_subset, hbody⟩ := h
  refine ⟨hwf, cs, S0, t0, hresolve, hcs_wf, hR0_subset, ?_⟩
  intro i hij st'' m'' denot hwle'' hdenot_proper himply_S2
  have hwle_base := WorldLe.trunc_step hjk hij hwle hwle''
  have hS_at : (Ty.shape_val_denot env S2).ImplyAfter i st'' m'' (Ty.shape_val_denot env S1) :=
    IPreDenot.imply_after_worldle
      (IPreDenot.ImplyAfter.trunc (Nat.le_trans hij hjk) (hS env k st m hts)) hwle_base
  have himply_S1 : denot.ImplyAfter i st'' m'' (Ty.shape_val_denot env S1) :=
    IPreDenot.ImplyAfter.trans himply_S2 hS_at
  have hb := hbody i hij st'' m'' denot hwle'' hdenot_proper himply_S1
  have henv' : EnvTyping (Γ,X<:S2) (env.extend_tvar denot) i st'' m'' :=
    ⟨hdenot_proper, himply_S2, env_typing_worldle_trunc _ hts hwle_base⟩
  exact ExpDenot.imply_after (hT (env.extend_tvar denot) i st'' m'' henv') hb

theorem fundamental_subtyp
  (hT1 : T1.IsClosed) (hT2 : T2.IsClosed)
  (hsub : Subtyp Γ T1 T2) :
  SemSubtyp Γ T1 T2 := by
  induction hsub
  case top =>
    apply sem_subtyp_top
  case refl =>
    apply sem_subtyp_refl
  case trans T2_mid hT2_mid _hsub12 _hsub23 ih12 ih23 =>
    apply sem_subtyp_trans (ih12 hT1 hT2_mid) (ih23 hT2_mid hT2)
  case tvar hlookup =>
    apply sem_subtyp_tvar hlookup
  case arrow T1_arg T2_arg U1 U2 hsub_arg hsub_res ih_arg ih_res =>
    cases hT1 with | arrow hT1_arg_closed hU1_closed =>
    cases hT2 with | arrow hT2_arg_closed hU2_closed =>
    apply sem_subtyp_arrow (ih_arg hT2_arg_closed hT1_arg_closed) (ih_res hU1_closed hU2_closed)
  case poly S1 S2 T1_body T2_body hsub_bound hsub_body ih_bound ih_body =>
    cases hT1 with | poly hS1_closed hT1_body_closed =>
    cases hT2 with | poly hS2_closed hT2_body_closed =>
    apply sem_subtyp_poly (ih_bound hS2_closed hS1_closed) (ih_body hT1_body_closed hT2_body_closed)
  case cpoly cb1 cb2 T1_body T2_body hsub_bound hsub_body ih_body =>
    cases hT1 with | cpoly hcb2_closed hT1_body_closed =>
    cases hT2 with | cpoly hcb1_closed hT2_body_closed =>
    have ih_bound := fundamental_subbound hsub_bound
    apply sem_subtyp_cpoly ih_bound (ih_body hT1_body_closed hT2_body_closed) hcb1_closed
  case capt C1 C2 S1 S2 hsub_capt hsub_shape ih_shape =>
    cases hT1 with | capt hC1_closed hS1_closed =>
    cases hT2 with | capt hC2_closed hS2_closed =>
    have ih_capt := fundamental_subcapt hsub_capt
    apply sem_subtyp_capt ih_capt (ih_shape hS1_closed hS2_closed) hC2_closed
  case exi T1_body T2_body hsub_body ih_body =>
    cases hT1 with | exi hT1_body_closed =>
    cases hT2 with | exi hT2_body_closed =>
    apply sem_subtyp_exi (ih_body hT1_body_closed hT2_body_closed)
  case typ T1_body T2_body hsub_body ih_body =>
    cases hT1 with | typ hT1_body_closed =>
    cases hT2 with | typ hT2_body_closed =>
    apply sem_subtyp_typ (ih_body hT1_body_closed hT2_body_closed)

theorem sem_typ_subtyp
  {C1 C2 : CaptureSet s} {E1 E2 : Ty .exi s}
  (ht : C1 # Γ ⊨ e : E1)
  (hsubcapt : Subcapt Γ C1 C2)
  (hsubtyp : Subtyp Γ E1 E2)
  (hclosed_E1 : E1.IsClosed)
  (hclosed_E2 : E2.IsClosed) :
  C2 # Γ ⊨ e : E2 := by
  intro env k st m htyping
  have h1 := ht env k st m htyping
  have hsc := fundamental_subcapt hsubcapt env k st m htyping
  have hst := fundamental_subtyp hclosed_E1 hclosed_E2 hsubtyp env k st m htyping
  exact ExpDenot.imply_after hst (ExpDenot.mono_auth hsc h1)

/-! ## The fundamental theorem -/

/-- The fundamental theorem of semantic type soundness: syntactic typing implies semantic
typing. -/
theorem fundamental
  (ht : C # Γ ⊢ e : T) :
  C # Γ ⊨ e : T := by
  have hclosed_e := HasType.exp_is_closed ht
  induction ht
  case var hx => apply sem_typ_var hx
  case abs =>
    apply sem_typ_abs
    · exact hclosed_e
    · cases hclosed_e; aesop
  case tabs =>
    apply sem_typ_tabs
    · exact hclosed_e
    · cases hclosed_e; aesop
  case cabs =>
    apply sem_typ_cabs
    · exact hclosed_e
    · cases hclosed_e; aesop
  case pack =>
    rename_i ih
    apply sem_typ_pack
    · exact hclosed_e
    · cases hclosed_e with | pack _ hx_closed =>
      apply ih
      constructor
      exact hx_closed
  case unit => exact sem_typ_unit
  case btrue => exact sem_typ_btrue
  case bfalse => exact sem_typ_bfalse
  case cond ht1 ht2 ht3 ih1 ih2 ih3 =>
    cases hclosed_e with
    | cond hclosed_guard hclosed_then hclosed_else =>
      exact sem_typ_cond (ih1 (Exp.IsClosed.var hclosed_guard)) (ih2 hclosed_then)
        (ih3 hclosed_else)
  case app =>
    rename_i hx hy
    cases hclosed_e with
    | app hx_closed hy_closed =>
      cases hx_closed
      cases hy_closed
      exact sem_typ_app
        (hx (Exp.IsClosed.var Var.IsClosed.bound))
        (hy (Exp.IsClosed.var Var.IsClosed.bound))
  case invoke =>
    rename_i hx hy
    cases hclosed_e with
    | app hx_closed hy_closed =>
      cases hx_closed
      cases hy_closed
      exact sem_typ_invoke
        (hx (Exp.IsClosed.var Var.IsClosed.bound))
        (hy (Exp.IsClosed.var Var.IsClosed.bound))
  case tapp =>
    rename_i hS_closed hx
    cases hclosed_e with
    | tapp hx_closed hS_closed =>
      cases hx_closed
      exact sem_typ_tapp
        (hx (Exp.IsClosed.var Var.IsClosed.bound))
  case capp =>
    rename_i hx hD_closed hih
    cases hclosed_e with
    | capp hx_closed hD_closed_exp =>
      cases hx_closed
      exact sem_typ_capp hD_closed_exp
        (hih (Exp.IsClosed.var Var.IsClosed.bound))
  case letin =>
    rename_i ht1_syn ht2_syn ht1_ih ht2_ih
    cases hclosed_e with
    | letin he1_closed he2_closed =>
      exact sem_typ_letin
        (HasType.use_set_is_closed ht1_syn)
        (ht1_ih he1_closed)
        (ht2_ih he2_closed)
  case unpack =>
    rename_i ht_syn _hu_syn ht_ih hu_ih
    cases hclosed_e with
    | unpack ht_closed hu_closed =>
      exact sem_typ_unpack
        (HasType.use_set_is_closed ht_syn)
        (ht_ih ht_closed)
        (hu_ih hu_closed)
  case alloc =>
    rename_i hx_syn hx_ih
    cases hclosed_e with
    | alloc hx_closed =>
      cases hx_closed
      exact sem_typ_alloc
        (hx_ih (Exp.IsClosed.var Var.IsClosed.bound))
  case read =>
    rename_i hx_syn hx_ih
    cases hclosed_e with
    | read hx_closed =>
      cases hx_closed
      exact sem_typ_read
        (hx_ih (Exp.IsClosed.var Var.IsClosed.bound))
  case write =>
    rename_i hx_syn hy_syn hx_ih hy_ih
    cases hclosed_e with
    | write hx_closed hy_closed =>
      cases hx_closed
      cases hy_closed
      exact sem_typ_write
        (hx_ih (Exp.IsClosed.var Var.IsClosed.bound))
        (hy_ih (Exp.IsClosed.var Var.IsClosed.bound))
  case subtyp ht_syn hsubcapt hsubtyp hclosed_C2 hclosed_E2 ht_ih =>
    have hclosed_E1 := HasType.type_is_closed ht_syn
    apply sem_typ_subtyp (ht_ih hclosed_e) hsubcapt hsubtyp hclosed_E1 hclosed_E2

end CC
