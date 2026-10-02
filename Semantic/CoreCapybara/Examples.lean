import Semantic.CoreCapybara.Fundamental

/-!
# Worked examples for owned splitting

Typing derivations, checked against the extended CoreCapybara rules, for programs that use
`split`, `concat`, `idx`, pairs and `par`.  By `fundamental`, each typed term is semantically
well typed, so the adequacy results (type safety, memory safety, data-race freedom) apply.
-/

-- De Bruijn indices in the concrete derivations below make some lines long.
set_option linter.style.longLine false

namespace CoreCapybara


/-! ## Tactics for capture-set inclusion and subcapturing on concrete terms -/

syntax "subset_tac" : tactic
macro_rules
  | `(tactic| subset_tac) => `(tactic| first
      | exact CaptureSet.Subset.refl
      | exact CaptureSet.Subset.empty
      | (apply CaptureSet.Subset.union_left <;> subset_tac)
      | (apply CaptureSet.Subset.union_right_left; subset_tac)
      | (apply CaptureSet.Subset.union_right_right; subset_tac))

/-! ## Evaluating `peaks` on concrete contexts -/

@[simp] theorem peaks_empty' (Γ : Ctx s) : CaptureSet.peaks Γ .empty = .empty := by
  rw [CaptureSet.peaks]
@[simp] theorem peaks_cvar' (Γ : Ctx s) : CaptureSet.peaks Γ (.cvar m c) = .cvar m c := by
  rw [CaptureSet.peaks]
@[simp] theorem peaks_union' (Γ : Ctx s) (a b : CaptureSet s) :
    CaptureSet.peaks Γ (.union a b) = .union (CaptureSet.peaks Γ a) (CaptureSet.peaks Γ b) := by
  rw [CaptureSet.peaks]; rfl
@[simp] theorem peaks_bound' (Γ : Ctx s) :
    CaptureSet.peaks Γ (.var m (.bound x)) = CaptureSet.peaksVarBound Γ m x := by
  rw [CaptureSet.peaks]
@[simp] theorem peaksVarBound_here' (Γ : Ctx s) (T : Ty .capt s) :
    CaptureSet.peaksVarBound (.push Γ (.var T)) m .here
      = ((CaptureSet.peaks Γ T.captureSet).rename Rename.succ).applyAccess m := by
  rw [CaptureSet.peaksVarBound]
@[simp] theorem peaksVarBound_there' (Γ : Ctx s) (b : Binding s k) (x : BVar s .var) :
    CaptureSet.peaksVarBound (.push Γ b) m (.there x)
      = (CaptureSet.peaksVarBound Γ m x).rename Rename.succ := by
  rw [CaptureSet.peaksVarBound]

/-! ## Evaluating renamings on concrete variables -/

@[simp] theorem rn_succ_var (x : BVar s k) : (Rename.succ (k := k0)).var x = x.there := rfl
@[simp] theorem rn_lift_here (f : Rename s1 s2) :
    (f.lift (k := k)).var (BVar.here : BVar (s1,,k) k) = .here := rfl
@[simp] theorem rn_lift_there (f : Rename s1 s2) (x : BVar s1 k) :
    (f.lift (k := k0)).var x.there = (f.var x).there := rfl
@[simp] theorem rn_comp_var (f : Rename s1 s2) (g : Rename s2 s3) (x : BVar s1 k) :
    (f.comp g).var x = g.var (f.var x) := rfl
@[simp] theorem rn_id_var (x : BVar s k) : (Rename.id).var x = x := rfl

/-- Normalizes renamed concrete capture sets in the goal. -/
macro "rn_norm" : tactic => `(tactic| (
  simp only [CaptureSet.rename, Var.rename, rn_succ_var, rn_lift_here, rn_lift_there,
    rn_comp_var, rn_id_var, Rename.weakenCVars, CaptureSet.freshCVars, CaptureSet.applyAccess,
    CaptureSet.applyDrop, CaptureSet.applyMut, Ty.captureSet, Ty.rename];
  repeat (first | erw [rn_lift_there] | erw [rn_lift_here] | erw [rn_succ_var])))

theorem sc_var_trans {Γ : Ctx s} {x : BVar s .var} {T : Ty .capt s} {C : CaptureSet s}
    (hlk : Γ.LookupVar x T) (hrest : Subcapt Γ T.captureSet C) :
    Subcapt Γ (.var (.M .epsilon) (.bound x)) C :=
  .sc_trans (.sc_var hlk) hrest

theorem sc_dropvar_trans {Γ : Ctx s} {x : BVar s .var} {T : Ty .capt s} {C : CaptureSet s}
    (hlk : Γ.LookupVar x T) (hrest : Subcapt Γ (T.captureSet.applyAccess .drop) C) :
    Subcapt Γ (.var .drop (.bound x)) C :=
  .sc_trans (.sc_drop_mono (C1 := .var (.M .epsilon) (.bound x)) (.sc_var hlk)) hrest

syntax "sc_tac" : tactic
macro_rules
  | `(tactic| sc_tac) => `(tactic| first
      | (apply Subcapt.sc_elem; subset_tac)
      | (apply Subcapt.sc_union <;> sc_tac)
      | exact sc_var_trans (by repeat constructor) (by (try rn_norm); sc_tac)
      | exact sc_dropvar_trans (by repeat constructor) (by (try rn_norm); sc_tac))

theorem sep_left_var {Γ : Ctx s} {x : BVar s .var} {T : Ty .capt s} {C : CaptureSet s}
    (hlk : Γ.LookupVar x T) (h : SepCheck Γ T.captureSet C) :
    SepCheck Γ (.var (.M .epsilon) (.bound x)) C :=
  .sep_mono h (.sc_var hlk)

theorem sep_left_dropvar {Γ : Ctx s} {x : BVar s .var} {T : Ty .capt s} {C : CaptureSet s}
    (hlk : Γ.LookupVar x T) (h : SepCheck Γ (T.captureSet.applyAccess .drop) C) :
    SepCheck Γ (.var .drop (.bound x)) C :=
  .sep_mono h (.sc_drop_mono (C1 := .var (.M .epsilon) (.bound x)) (.sc_var hlk))

/-- Distinctness of two concrete de Bruijn indices. -/
macro "neq_tac" : tactic => `(tactic| (intro h; simp [Rename.succ] at h <;> cases h))

/-- Separation of concrete capture sets: split unions, look variables up, and
separate distinct droppable roots. -/
syntax "sep_tac" : tactic
macro_rules
  | `(tactic| sep_tac) => `(tactic| first
      | exact SepCheck.sep_empty
      | exact SepCheck.sep_symm SepCheck.sep_empty
      | (apply SepCheck.sep_union <;> sep_tac)
      | (apply SepCheck.sep_symm; apply SepCheck.sep_union <;> (apply SepCheck.sep_symm; sep_tac))
      | exact SepCheck.sep_droppable ⟨rfl, rfl, by neq_tac⟩
      | exact SepCheck.sep_droppable ⟨rfl, rfl, by intro h; cases h⟩
      | exact sep_left_var (by repeat constructor) (by (try rn_norm); sep_tac)
      | exact sep_left_dropvar (by repeat constructor) (by (try rn_norm); sep_tac)
      | exact SepCheck.sep_symm (sep_left_var (by repeat constructor) (by (try rn_norm); (apply SepCheck.sep_symm); sep_tac))
      | exact SepCheck.sep_symm (sep_left_dropvar (by repeat constructor) (by (try rn_norm); (apply SepCheck.sep_symm); sep_tac)))

theorem kill_cvar_there' (Γ : Ctx s) (b : Binding s k) (c : BVar s .cvar) :
    (Γ.push b).kill_cvar c.there = (Γ.kill_cvar c).push b := by
  rw [Ctx.kill_cvar]
theorem kill_cvar_here' (Γ : Ctx s) (cb : CaptureBound s) :
    (Γ.push (.cvar a cb)).kill_cvar .here = Γ.push (.cvar .killed cb) := by
  rw [Ctx.kill_cvar]

theorem kill_peaks_empty' (Γ : Ctx s) :
    Γ.kill_peaks ((({} : CaptureSet s)).peakset Γ).consumed = Γ := by
  simp only [Ctx.kill_peaks, CaptureSet.peakset, PeakSet.consumed]
  erw [peaks_empty']
  rfl

/-- A `letin` whose head uses no capability. -/
theorem HasType.letin_pure {Γ : Ctx s} {e1 : Exp s} {e2 : Exp (s,x)} {T : Ty .capt s}
    {C2 : CaptureSet s} {U : Ty .exi s}
    (hC2 : C2.IsClosed) (hU : U.IsClosed)
    (h1 : HasType {} Γ e1 (.typ T))
    (h2 : HasType (C2.rename Rename.succ) (Γ,x:T) e2 (U.rename Rename.succ)) :
    HasType C2 Γ (.letin e1 e2) U := by
  have h := HasType.letin (C2 := C2) (.seq_sep .sep_empty) h1 (by rw [kill_peaks_empty']; exact h2)
  exact HasType.subtyp h (.sc_union (.sc_elem .empty) (.sc_elem .refl)) .refl hC2 hU

def ΓA : Ctx (({},C),x) :=
  (Ctx.empty ,C[.can_drop]<: .unbound) ,x: (.arr (.cvar (.M .epsilon) .here) .unit)

theorem ΓA_closed : ΓA.IsClosed := by
  repeat constructor

theorem ΓA_split : HasType ((.var (.M .epsilon) (.bound .here)) ∪ (.var .drop (.bound .here))) ΓA
    (.split (.bound .here) 1)
    (.exi 2 (Ty.splitBody (.var (.M .epsilon) (.bound .here)) .unit)) := by
  apply HasType.split ΓA_closed
  · intro a c h
    simp only [CaptureSet.peakset] at h
    erw [peaks_bound', peaksVarBound_here'] at h
    simp [Ty.captureSet, CaptureSet.rename, CaptureSet.applyAccess, CaptureSet.applyMut,
      Rename.succ] at h
    obtain ⟨_, rfl⟩ := CaptureSet.cvar_subset_cvar_inv h
    rfl
  · exact HasType.var ΓA_closed .here

/-- After the split, the parent's root is killed. -/
def ΓAk : Ctx (({},C),x) :=
  (Ctx.empty ,C[.killed]<: .unbound) ,x: (.arr (.cvar (.M .epsilon) .here) .unit)

set_option hygiene false in
macro "auto_closed" : tactic => `(tactic| (
  (try simp only [Ctx.push_var, Ctx.push_lock, Ctx.extendCVars, Ctx.push_cvar, ΓAk, Ty.rename,
    CaptureSet.rename, Var.rename, Ty.splitBody, CaptureSet.freshCVars, CaptureSet.applyAccess,
    CaptureSet.applyDrop, CaptureSet.applyMut, ModalCtx.rename, SepCtx.rename,
    MutabilityCtx.rename]);
  repeat (first | constructor | rfl)))

set_option hygiene false in
macro "peaks_at" h:ident : tactic => `(tactic| (
  simp only [PeakSet.consumed, CaptureSet.peakset] at $h:ident;
  repeat (first
    | erw [peaks_union'] at $h:ident
    | erw [peaks_bound'] at $h:ident
    | erw [peaksVarBound_here'] at $h:ident
    | erw [peaksVarBound_there'] at $h:ident
    | erw [peaks_cvar'] at $h:ident
    | erw [peaks_empty'] at $h:ident);
  simp [Ty.captureSet, CaptureSet.rename, Var.rename, CaptureSet.applyAccess, CaptureSet.applyMut,
    CaptureSet.applyDrop, CaptureSet.consumed, Rename.succ, Rename.lift, Ty.rename] at $h:ident))

set_option hygiene false in
macro "cvar_cases" h:ident : tactic => `(tactic| (
  iterate 6 (all_goals try (rcases CaptureSet.cvar_subset_union_inv $h:ident with $h:ident | $h:ident));
  all_goals first
    | exact absurd $h:ident CaptureSet.cvar_not_subset_empty
    | (obtain ⟨_, rfl⟩ := CaptureSet.cvar_subset_cvar_inv $h:ident; rfl)))

theorem ΓA_kill : ΓA.kill_peaks ((CaptureSet.peakset ΓA
    ((.var (.M .epsilon) (.bound .here)) ∪ (.var .drop (.bound .here)))).consumed) = ΓAk := by
  simp only [Ctx.kill_peaks, PeakSet.consumed, CaptureSet.peakset]
  erw [peaks_union', peaks_bound', peaks_bound', peaksVarBound_here', peaksVarBound_here']
  simp [Ty.captureSet, CaptureSet.rename, CaptureSet.applyAccess, CaptureSet.applyMut,
    CaptureSet.applyDrop, CaptureSet.consumed, Rename.succ, ΓA, ΓAk, Ctx.kill_peaks_cs,
    Ctx.push_var, Ctx.push_cvar]
  rfl

/-- The continuation of the round trip: project the halves, join them, split again. -/
def rtCont : Exp ((((({},C),x).extendCVars 2),x)) :=
  .letin (.fst (.bound .here))
    (.letin (.snd (.bound (.there .here)))
      (.letin (.concat (.bound (.there .here)) (.bound .here))
        (.unpack 2 (.split (.bound .here) 1) .unit)))

/-- **Round trip.** Split an owned array, join the two halves (their separation is derived
by the unchanged `sep_droppable` rule), and split the joined array again (its peaks are the
two fresh, droppable roots). -/
theorem roundTrip_typed : HasType ((.var (.M .epsilon) (.bound .here)) ∪ (.var .drop (.bound .here))) ΓA
    (.unpack 2 (.split (.bound .here) 1) rtCont) (.typ .unit) := by
  have h := HasType.unpack (C2 := {}) (U := .typ .unit) (u := rtCont) (n := 2)
    (Γ := ΓA) ?seq ?drop ΓA_split ?cont
  · exact HasType.subtyp h
      (.sc_union (.sc_elem .refl) (.sc_elem .empty)) .refl
      (by repeat constructor) (by repeat constructor)
  case seq => exact .seq_sep (.sep_symm .sep_empty)
  case drop =>
    intro a c h
    simp only [PeakSet.consumed, CaptureSet.peakset] at h
    erw [peaks_union', peaks_bound', peaks_bound', peaksVarBound_here',
      peaksVarBound_here'] at h
    simp [Ty.captureSet, CaptureSet.rename, CaptureSet.applyAccess, CaptureSet.applyMut,
      CaptureSet.applyDrop, CaptureSet.consumed, Rename.succ] at h
    rcases CaptureSet.cvar_subset_union_inv h with h | h
    · exact absurd h CaptureSet.cvar_not_subset_empty
    · obtain ⟨_, rfl⟩ := CaptureSet.cvar_subset_cvar_inv h; rfl
  case cont =>
    erw [ΓA_kill]
    refine HasType.letin_pure ?c1 ?u1 (HasType.fst (HasType.var ?cl .here)) ?k1
    case cl => auto_closed
    case c1 => auto_closed
    case u1 => auto_closed
    case k1 =>
      refine HasType.letin_pure ?c2 ?u2 (HasType.snd (HasType.var ?cl2 (.there .here))) ?k2
      case cl2 => auto_closed
      case c2 => auto_closed
      case u2 => auto_closed
      case k2 =>
        refine HasType.letin_pure ?c3 ?u3
          (HasType.concat (HasType.var ?cl3 (.there .here)) (HasType.var ?cl3' .here) ?sep) ?k3
        case cl3 => auto_closed
        case cl3' => auto_closed
        case c3 => auto_closed
        case u3 => auto_closed
        case sep =>
          refine SepCheck.sep_mono (SepCheck.sep_symm (SepCheck.sep_mono
            (SepCheck.sep_droppable ⟨rfl, rfl, by intro h; simp [Rename.succ] at h⟩) (Subcapt.sc_var .here)))
            (Subcapt.sc_var (.there .here))
        case k3 =>
          refine HasType.subtyp
            (HasType.unpack (C2 := {}) (.seq_sep (.sep_symm .sep_empty)) ?dr4
              (HasType.split ?cl4 ?dr4' (HasType.var ?cl4' .here))
              (HasType.subtyp HasType.unit (.sc_elem .empty) .refl
                (by repeat constructor) (by repeat constructor)))
            ?sc4 .refl ?cc4 ?ec4
          case cl4 => auto_closed
          case cl4' => auto_closed
          case dr4 =>
            intro a c h
            peaks_at h
            cvar_cases h
          case dr4' =>
            intro a c h
            peaks_at h
            cvar_cases h
          case cc4 => auto_closed
          case ec4 => auto_closed
          case sc4 =>
            refine .sc_union (.sc_union ?A ?B) (.sc_elem .empty)
            case A =>
              refine .sc_trans (.sc_var .here) ?A1
              refine .sc_union (.sc_trans (.sc_var (.there (.there .here))) ?ha)
                (.sc_trans (.sc_var (.there .here)) ?hb)
              case ha =>
                apply Subcapt.sc_elem
                simp only [Ty.captureSet, Ty.rename, CaptureSet.rename, CaptureSet.freshCVars]
                exact .union_right_left (.union_right_right (.union_right_left .refl))
              case hb =>
                apply Subcapt.sc_elem
                simp only [Ty.captureSet, Ty.rename, CaptureSet.rename, CaptureSet.freshCVars]
                exact .union_right_left (.union_right_right (.union_right_right (.union_right_left .refl)))
            case B =>
              refine .sc_trans (.sc_drop_mono (C1 := .var (.M .epsilon) (.bound .here))
                (C2 := .union (.cvar (.M .epsilon) (.there (.there (.there (.there (.there .here))))))
                  (.cvar (.M .epsilon) (.there (.there (.there (.there (.there (.there .here)))))))) ?D) ?hd
              case D =>
                refine .sc_trans (.sc_var .here) ?D1
                exact .sc_union (.sc_trans (.sc_var (.there (.there .here))) (.sc_elem (.union_right_left .refl)))
                  (.sc_trans (.sc_var (.there .here)) (.sc_elem (.union_right_right .refl)))
              apply Subcapt.sc_elem
              simp only [CaptureSet.rename, CaptureSet.freshCVars,
                CaptureSet.applyAccess, CaptureSet.applyDrop]
              exact .union_left (.union_right_right (.union_right_left .refl))
                (.union_right_right (.union_right_right (.union_right_left .refl)))

/-- The round trip is semantically well typed (fundamental theorem). -/
theorem roundTrip_sound : SemanticTyping
    ((.var (.M .epsilon) (.bound .here)) ∪ (.var .drop (.bound .here))) ΓA
    (.unpack 2 (.split (.bound .here) 1) rtCont) (.typ .unit) :=
  fundamental ΓA_closed roundTrip_typed


/-! ## `process`: split, write both halves in parallel, consume one, return the other -/

abbrev SigP : Sig := (((((((({},C),x),C),x),C),x),x),x)

/-- Context of the body of `process(consume buf)`: the owned array `buf`, two owned fallback
cells `e1`, `e2` (for indexing), a unit value `u`, and a consumer `send`. -/
def ΓP : Ctx SigP :=
  ((((((((Ctx.empty ,C[.can_drop]<: .unbound)
    ,x: (.arr (.cvar (.M .epsilon) .here) .unit))
    ,C[.can_drop]<: .unbound)
    ,x: (.cell (.cvar (.M .epsilon) .here) .unit))
    ,C[.can_drop]<: .unbound)
    ,x: (.cell (.cvar (.M .epsilon) .here) .unit))
    ,x: .unit)
    ,x: (.consumer (.exi 1 (.arr (.cvar (.M .epsilon) .here) .unit)) {} (.typ .unit)))


/-- The body of `process` after `split`: `p` holds the pair of halves. -/
def procCont : Exp ((SigP.extendCVars 2),x) :=
  .letin (.fst (.bound .here))                                   -- hdr
  (.letin (.snd (.bound (.there .here)))                                  -- body
  (.letin (.par ((.var (.M .epsilon) (.bound (.there .here))) ∪ (.var (.M .epsilon) (.bound (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) ((.var (.M .epsilon) (.bound .here)) ∪ (.var (.M .epsilon) (.bound (.there (.there (.there (.there (.there (.there (.there .here))))))))))
      (.letin (.idx (.bound (.there .here)) 0 (.bound (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.write (.bound .here) (.bound (.there (.there (.there (.there (.there (.there (.there .here))))))))))   -- hdr[0] := u
      (.letin (.idx (.bound .here) 0 (.bound (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.write (.bound .here) (.bound (.there (.there (.there (.there (.there (.there (.there .here)))))))))))  -- body[0] := u
  (.letin (.consumer_app (.bound (.there (.there (.there (.there (.there (.there .here))))))) (.pack ⟨[(.var (.M .epsilon) (.bound (.there .here)))], rfl⟩ (.bound (.there .here))))   -- send(body)
  (.pack ⟨[(.var (.M .epsilon) (.bound (.there (.there (.there .here)))))], rfl⟩ (.bound (.there (.there (.there .here))))))))                     -- return hdr as fresh

/-- **process.** `split buf`, write both halves in parallel, send one half, return the other
as a fresh array. -/
def procBody : Exp SigP :=
  .unpack 2 (.split (.bound (.there (.there (.there (.there (.there (.there .here))))))) 1) procCont


set_option hygiene false in
macro "cvar_cases_acc" h:ident : tactic => `(tactic| (
  iterate 6 (all_goals try (rcases CaptureSet.cvar_subset_union_inv $h:ident with $h:ident | $h:ident));
  all_goals first
    | exact absurd $h:ident CaptureSet.cvar_not_subset_empty
    | (obtain ⟨_, rfl⟩ := CaptureSet.cvar_subset_cvar_inv $h:ident; intro hk; cases hk)))

set_option hygiene false in
macro "cvar_cases_ao" h:ident : tactic => `(tactic| (
  iterate 6 (all_goals try (rcases CaptureSet.cvar_subset_union_inv $h:ident with $h:ident | $h:ident));
  all_goals first
    | exact absurd $h:ident CaptureSet.cvar_not_subset_empty
    | (have := CaptureSet.cvar_subset_cvar_inv $h:ident; cases this.1)))

set_option hygiene false in
macro "peaks_goal" : tactic => `(tactic| (
  simp only [Ctx.kill_peaks, PeakSet.consumed, CaptureSet.peakset];
  repeat (first | erw [peaks_union'] | erw [peaks_bound'] | erw [peaksVarBound_here'] | erw [peaksVarBound_there'] | erw [peaks_cvar'] | erw [peaks_empty']);
  simp only [Ty.captureSet, CaptureSet.rename, Var.rename, CaptureSet.applyAccess,
    CaptureSet.applyMut, CaptureSet.applyDrop, CaptureSet.consumed, Ty.rename,
    Ctx.kill_peaks_cs]))

theorem ΓP_closed : ΓP.IsClosed := by
  repeat constructor

/-- After the split, `buf`'s root is killed. -/
def ΓPk : Ctx SigP :=
  ((((((((Ctx.empty ,C[.killed]<: .unbound)
    ,x: (.arr (.cvar (.M .epsilon) .here) .unit))
    ,C[.can_drop]<: .unbound)
    ,x: (.cell (.cvar (.M .epsilon) .here) .unit))
    ,C[.can_drop]<: .unbound)
    ,x: (.cell (.cvar (.M .epsilon) .here) .unit))
    ,x: .unit)
    ,x: (.consumer (.exi 1 (.arr (.cvar (.M .epsilon) .here) .unit)) {} (.typ .unit)))

theorem ΓP_kill : ΓP.kill_peaks ((CaptureSet.peakset ΓP
    ((.var (.M .epsilon) (.bound (.there (.there (.there (.there (.there (.there .here)))))))) ∪ (.var .drop (.bound (.there (.there (.there (.there (.there (.there .here)))))))))).consumed) = ΓPk := by
  simp only [Ctx.kill_peaks, PeakSet.consumed, CaptureSet.peakset]
  repeat (first | erw [peaks_union'] | erw [peaks_bound'] | erw [peaksVarBound_here'] | erw [peaksVarBound_there'])
  simp [Ty.captureSet, CaptureSet.rename, CaptureSet.applyAccess, CaptureSet.applyMut,
    CaptureSet.applyDrop, CaptureSet.consumed, Rename.succ, ΓP, ΓPk, Ctx.kill_peaks_cs,
    Ctx.push_var, Ctx.push_cvar]
  rfl

theorem ΓP_split : HasType ((.var (.M .epsilon) (.bound (.there (.there (.there (.there (.there (.there .here)))))))) ∪ (.var .drop (.bound (.there (.there (.there (.there (.there (.there .here))))))))) ΓP (.split (.bound (.there (.there (.there (.there (.there (.there .here))))))) 1)
    (.exi 2 (Ty.splitBody (.var (.M .epsilon) (.bound (.there (.there (.there (.there (.there (.there .here)))))))) .unit)) := by
  apply HasType.split ΓP_closed
  · intro a c h
    peaks_at h
    cvar_cases h
  · exact HasType.var ΓP_closed (.there (.there (.there (.there (.there (.there .here))))))

theorem procBody_typed : HasType (((.var (.M .epsilon) (.bound (.there (.there (.there (.there (.there (.there .here)))))))) ∪ (.var .drop (.bound (.there (.there (.there (.there (.there (.there .here))))))))) ∪ ((.var (.M .epsilon) (.bound (.there (.there (.there (.there .here)))))) ∪ (.var (.M .epsilon) (.bound (.there (.there .here)))) ∪ (.var (.M .epsilon) (.bound .here))))
    ΓP procBody (.exi 1 (.arr (.cvar (.M .epsilon) .here) .unit)) := by
  refine HasType.unpack (C2 := (.var (.M .epsilon) (.bound (.there (.there (.there (.there .here)))))) ∪ (.var (.M .epsilon) (.bound (.there (.there .here)))) ∪ (.var (.M .epsilon) (.bound .here))) ?seq ?drop ΓP_split ?cont
  case seq =>
    exact .seq_sep (.sep_union
      (.sep_symm (.sep_union (.sep_union (.sep_symm (.sep_mono (.sep_symm (.sep_mono (.sep_droppable ⟨rfl, rfl, by neq_tac⟩) (.sc_var (.there (.there (.there (.there .here))))))) (.sc_var (.there (.there (.there (.there (.there (.there .here))))))))) (.sep_symm (.sep_mono (.sep_symm (.sep_mono (.sep_droppable ⟨rfl, rfl, by neq_tac⟩) (.sc_var (.there (.there .here))))) (.sc_var (.there (.there (.there (.there (.there (.there .here))))))))))
        (.sep_symm (.sep_symm (.sep_mono .sep_empty (.sc_var .here))))))
      (.sep_symm (.sep_union (.sep_union (.sep_symm (.sep_mono (.sep_symm (.sep_mono (.sep_droppable ⟨rfl, rfl, by neq_tac⟩) (.sc_var (.there (.there (.there (.there .here))))))) (.sc_drop_mono (C1 := .var (.M .epsilon) (.bound (.there (.there (.there (.there (.there (.there .here)))))))) (.sc_var (.there (.there (.there (.there (.there (.there .here)))))))))) (.sep_symm (.sep_mono (.sep_symm (.sep_mono (.sep_droppable ⟨rfl, rfl, by neq_tac⟩) (.sc_var (.there (.there .here))))) (.sc_drop_mono (C1 := .var (.M .epsilon) (.bound (.there (.there (.there (.there (.there (.there .here)))))))) (.sc_var (.there (.there (.there (.there (.there (.there .here)))))))))))
        (.sep_symm (.sep_symm (.sep_mono .sep_empty (.sc_var .here)))))))
  case drop =>
    intro a c h
    peaks_at h
    cvar_cases h
  case cont =>
    erw [ΓP_kill]
    refine HasType.letin_pure (by auto_closed) (by auto_closed)
      (HasType.fst (HasType.var (by auto_closed) .here)) ?k1
    refine HasType.letin_pure (by auto_closed) (by auto_closed)
      (HasType.snd (HasType.var (by auto_closed) (.there .here))) ?k2
    refine HasType.subtyp (HasType.letin (C1 := ?Cpar) (C2 := ((((.var (.M .epsilon) (.bound .here)) ∪ (.var .drop (.bound .here))) ∪ (.var (.M .epsilon) (.bound (.there (.there (.there (.there (.there (.there .here))))))))) ∪ ((.var (.M .epsilon) (.bound (.there .here))) ∪ (.var .drop (.bound (.there .here)))))) (T := ?Tpar) ?seqP ?par ?rest) ?scP .refl
      (by auto_closed) (by auto_closed)
    case par =>
      refine HasType.par (E1 := .typ .unit) (E2 := .typ .unit) ?b1 ?b2 ?sepP
      case b1 =>
        refine HasType.letin_pure ?cc ?uu
          (HasType.idx (HasType.var ?cl1 (.there .here)) (HasType.var ?cl2 (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) ?w
        case w =>
          refine HasType.subtyp
            (HasType.write ?acc (HasType.var ?cl3 .here) (HasType.var ?cl4 (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
            (.sc_var .here) .refl ?cc2 ?uu2
          case acc =>
            intro a c h
            peaks_at h
            cvar_cases_acc h
          all_goals auto_closed
        all_goals auto_closed
      case b2 =>
        refine HasType.letin_pure ?cc_b ?uu_b
          (HasType.idx (HasType.var ?cl1_b .here) (HasType.var ?cl2_b (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) ?w_b
        case w_b =>
          refine HasType.subtyp
            (HasType.write ?acc_b (HasType.var ?cl3_b .here) (HasType.var ?cl4_b (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
            (.sc_var .here) .refl ?cc2_b ?uu2_b
          case acc_b =>
            intro a c h
            peaks_at h
            cvar_cases_acc h
          all_goals auto_closed
        all_goals auto_closed
      case sepP =>
        exact .sep_union (.sep_symm (.sep_union (.sep_symm (.sep_mono (.sep_symm (.sep_mono (.sep_droppable ⟨rfl, rfl, by neq_tac⟩) (.sc_var .here))) (.sc_var (.there .here)))) (.sep_symm (.sep_mono (.sep_symm (.sep_mono (.sep_droppable ⟨rfl, rfl, by neq_tac⟩) (.sc_var (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.sc_var (.there .here))))))
          (.sep_symm (.sep_union (.sep_symm (.sep_mono (.sep_symm (.sep_mono (.sep_droppable ⟨rfl, rfl, by neq_tac⟩) (.sc_var .here))) (.sc_var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.sep_symm (.sep_mono (.sep_symm (.sep_mono (.sep_droppable ⟨rfl, rfl, by neq_tac⟩) (.sc_var (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.sc_var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))
    case seqP =>
      refine .seq_access_only (by auto_closed) ?_
      intro c h
      peaks_at h
      cvar_cases_ao h
    case scP =>
      rn_norm
      sc_tac
    case rest =>
      peaks_goal
      refine HasType.subtyp
        (HasType.letin (C1 := ?Cc) (C2 := (CaptureSet.union (CaptureSet.union (CaptureSet.var (.M .epsilon) (.bound (.there (.there .here)))) .empty) (CaptureSet.applyAccess .drop (CaptureSet.union (CaptureSet.var (.M .epsilon) (.bound (.there (.there .here)))) .empty)))) (T := .unit) ?seqR ?cons ?ret)
        ?scR .refl ?ccR ?ecR
      case cons =>
        refine HasType.consumer_app (T1 := ?T1c) (C1 := ?C1c) ?seqS ?dropS ?accS ?vS ?pk
        case vS =>
          refine HasType.var ?clvS (.there (.there (.there (.there (.there (.there (.there .here)))))))
          auto_closed
        case pk =>
          refine HasType.pack ?clPk ?aoPk ?drPk ?pwPk ?vB
          case vB =>
            refine HasType.var ?clvB (.there .here)
            auto_closed
          case aoPk =>
            intro c h
            try simp only [List.Vector.map, List.map, CaptureSet.rename, Var.rename] at h
            peaks_at h
            cvar_cases_ao h
          case drPk =>
            intro a c h
            try simp only [List.Vector.map, List.map, CaptureSet.rename, Var.rename] at h
            peaks_at h
            cvar_cases h
          case pwPk => exact List.pairwise_singleton _ _
          all_goals auto_closed
        case seqS =>
          refine .seq_sep ?_
          rn_norm
          sep_tac
        case dropS =>
          intro a c h
          try simp only [List.Vector.map, List.map, CaptureSet.rename, Var.rename] at h
          peaks_at h
          cvar_cases h
        case accS =>
          intro a c h
          peaks_at h
          cvar_cases_acc h
      case seqR =>
        refine .seq_sep ?_
        rn_norm
        sep_tac
      case ret =>
        simp only [List.Vector.map, List.map]
        peaks_goal
        rn_norm
        simp only [Ctx.push_var, Ctx.push_lock, Ctx.extendCVars, Ctx.push_cvar, ΓPk]
        repeat (first | erw [kill_cvar_there'] | erw [kill_cvar_here'])
        refine HasType.pack (Cs := ⟨[.var (.M .epsilon) (.bound (.there (.there (.there .here))))], rfl⟩) ?clR ?aoR ?drR ?pwR ?vR
        case vR =>
          refine HasType.var ?clvR (.there (.there (.there .here)))
          auto_closed
        case aoR =>
          intro c h
          try simp only [List.Vector.map, List.map, CaptureSet.rename, Var.rename] at h
          peaks_at h
          cvar_cases_ao h
        case drR =>
          intro a c h
          try simp only [List.Vector.map, List.map, CaptureSet.rename, Var.rename] at h
          peaks_at h
          cvar_cases h
        case pwR => exact List.pairwise_singleton _ _
        all_goals auto_closed
      case scR => sc_tac
      all_goals auto_closed


/-- `process` is semantically well typed (fundamental theorem): `hdr` outlives the split and
is returned as a fresh array while `body` is consumed. -/
theorem procBody_sound : SemanticTyping
    (((.var (.M .epsilon) (.bound (.there (.there (.there (.there (.there (.there .here)))))))) ∪ (.var .drop (.bound (.there (.there (.there (.there (.there (.there .here))))))))) ∪ ((.var (.M .epsilon) (.bound (.there (.there (.there (.there .here)))))) ∪ (.var (.M .epsilon) (.bound (.there (.there .here)))) ∪ (.var (.M .epsilon) (.bound .here))))
    ΓP procBody (.exi 1 (.arr (.cvar (.M .epsilon) .here) .unit)) :=
  fundamental ΓP_closed procBody_typed

#print axioms roundTrip_sound
#print axioms procBody_sound

end CoreCapybara
