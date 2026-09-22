import Semantic.CC.Semantics.Heap

/-!
# Traces of heap events

A run of a CC program is instrumented with a *trace* of the capability events it
performs.  Reads are singled out because they are the index-consuming events of the
step-indexed model (`Trace.readCount`); allocations are recorded so that a program
may freely use the cells it allocates itself (`TraceOkFrom`'s alloc exemption).
-/

namespace CC

/-- A heap event. -/
inductive TraceItem : Type where
/-- Dereference of the mutable cell `l` (index-consuming). -/
| read : Nat -> TraceItem
/-- Write to the mutable cell `l`, or invocation of the basic capability `l`. -/
| access : Nat -> TraceItem
/-- Allocation of the fresh mutable cell `l`. -/
| alloc : Nat -> TraceItem

/-- A trace is a list of heap events, in order. -/
abbrev Trace : Type := List TraceItem

/-- The number of reads in a trace: the step measure of the step-indexed model. -/
def Trace.readCount (t : Trace) : Nat :=
  t.countP (fun item => match item with | .read _ => true | _ => false)

@[simp] theorem Trace.readCount_nil : Trace.readCount [] = 0 := rfl

@[simp] theorem Trace.readCount_read (l : Nat) (t : Trace) :
    Trace.readCount (.read l :: t) = Trace.readCount t + 1 := by
  simp only [Trace.readCount, List.countP_cons]; rfl

@[simp] theorem Trace.readCount_access (l : Nat) (t : Trace) :
    Trace.readCount (.access l :: t) = Trace.readCount t := by
  simp only [Trace.readCount, List.countP_cons]; rfl

@[simp] theorem Trace.readCount_alloc (l : Nat) (t : Trace) :
    Trace.readCount (.alloc l :: t) = Trace.readCount t := by
  simp only [Trace.readCount, List.countP_cons]; rfl

@[simp] theorem Trace.readCount_append (t1 t2 : Trace) :
    (t1 ++ t2).readCount = t1.readCount + t2.readCount := by
  simp only [Trace.readCount, List.countP_append]

/-- The locations allocated by a trace. -/
def Trace.allocList : Trace -> List Nat
| [] => []
| .alloc l :: t => l :: Trace.allocList t
| .read _ :: t => Trace.allocList t
| .access _ :: t => Trace.allocList t

@[simp] theorem Trace.allocList_nil : Trace.allocList [] = [] := rfl
@[simp] theorem Trace.allocList_alloc (l : Nat) (t : Trace) :
    Trace.allocList (.alloc l :: t) = l :: Trace.allocList t := rfl
@[simp] theorem Trace.allocList_read (l : Nat) (t : Trace) :
    Trace.allocList (.read l :: t) = Trace.allocList t := rfl
@[simp] theorem Trace.allocList_access (l : Nat) (t : Trace) :
    Trace.allocList (.access l :: t) = Trace.allocList t := rfl

@[simp] theorem Trace.allocList_append (t1 t2 : Trace) :
    (t1 ++ t2).allocList = t1.allocList ++ t2.allocList := by
  induction t1 with
  | nil => rfl
  | cons it t1 ih => cases it <;> simp [Trace.allocList, ih]

/-- The capability set of a list of locations. -/
def CapabilitySet.ofList : List Nat -> CapabilitySet
| [] => {}
| l :: ls => .cap l ∪ CapabilitySet.ofList ls

theorem CapabilitySet.mem_ofList {x : Nat} {ls : List Nat} :
    x ∈ CapabilitySet.ofList ls ↔ x ∈ ls := by
  induction ls with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons l ls ih =>
    constructor
    · intro h
      cases h with
      | left h => cases h; exact List.mem_cons_self
      | right h => exact List.mem_cons_of_mem _ (ih.mp h)
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact CapabilitySet.mem.left CapabilitySet.mem.here
      · exact CapabilitySet.mem.right (ih.mpr h)

/-- **Trace authorization.**  `TraceOkFrom R A t`: every read/access event of `t` is on a
  location that is either in the authority `R` or was allocated earlier in the trace
  (the running allocated set starts at `A`).  A program may freely use the cells it
  allocates itself. -/
inductive TraceOkFrom (R : CapabilitySet) : List Nat -> Trace -> Prop where
| nil : TraceOkFrom R A []
| read : (l ∈ A ∨ l ∈ R) -> TraceOkFrom R A t -> TraceOkFrom R A (.read l :: t)
| access : (l ∈ A ∨ l ∈ R) -> TraceOkFrom R A t -> TraceOkFrom R A (.access l :: t)
| alloc : TraceOkFrom R (l :: A) t -> TraceOkFrom R A (.alloc l :: t)

/-- A trace is authorized by `R` when it is authorized from the empty allocated set. -/
def TraceOk (t : Trace) (R : CapabilitySet) : Prop := TraceOkFrom R [] t

theorem TraceOk.nil {R : CapabilitySet} : TraceOk [] R := TraceOkFrom.nil

theorem TraceOk.read {R : CapabilitySet} {l : Nat} (h : l ∈ R) : TraceOk [.read l] R :=
  TraceOkFrom.read (Or.inr h) TraceOkFrom.nil

theorem TraceOk.access {R : CapabilitySet} {l : Nat} (h : l ∈ R) : TraceOk [.access l] R :=
  TraceOkFrom.access (Or.inr h) TraceOkFrom.nil

theorem TraceOk.alloc {R : CapabilitySet} {l : Nat} : TraceOk [.alloc l] R :=
  TraceOkFrom.alloc TraceOkFrom.nil

/-- Authorization only depends on the allocated set up to membership. -/
theorem TraceOkFrom.congr {R : CapabilitySet} {A A' : List Nat} {t : Trace}
    (hA : ∀ l, l ∈ A -> l ∈ A') (h : TraceOkFrom R A t) : TraceOkFrom R A' t := by
  induction h generalizing A' with
  | nil => exact .nil
  | read hl _ ih => exact .read (hl.imp_left (hA _)) (ih hA)
  | access hl _ ih => exact .access (hl.imp_left (hA _)) (ih hA)
  | alloc _ ih =>
    refine .alloc (ih ?_)
    intro l' hl'
    rcases List.mem_cons.mp hl' with rfl | hl'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hA _ hl')

/-- Authorization is monotone in the authority. -/
theorem TraceOkFrom.mono {R R' : CapabilitySet} {A : List Nat} {t : Trace}
    (hsub : R ⊆ R') (h : TraceOkFrom R A t) : TraceOkFrom R' A t := by
  induction h with
  | nil => exact .nil
  | read hl _ ih => exact .read (hl.imp_right (CapabilitySet.subset_preserves_mem hsub)) ih
  | access hl _ ih => exact .access (hl.imp_right (CapabilitySet.subset_preserves_mem hsub)) ih
  | alloc _ ih => exact .alloc ih

theorem TraceOk.mono {R R' : CapabilitySet} {t : Trace}
    (hsub : R ⊆ R') (h : TraceOk t R) : TraceOk t R' :=
  TraceOkFrom.mono hsub h

/-- Authorization from an allocated set `A` can be traded for authority over `A`. -/
theorem TraceOkFrom.of_auth {R : CapabilitySet} {B A : List Nat} {t : Trace}
    (h : TraceOkFrom (R ∪ CapabilitySet.ofList B) A t) : TraceOkFrom R (B ++ A) t := by
  induction h with
  | nil => exact .nil
  | read hl _ ih =>
    refine .read ?_ ih
    rcases hl with hl | hl
    · exact Or.inl (List.mem_append_right _ hl)
    · cases hl with
      | left h => exact Or.inr h
      | right h => exact Or.inl (List.mem_append_left _ (CapabilitySet.mem_ofList.mp h))
  | access hl _ ih =>
    refine .access ?_ ih
    rcases hl with hl | hl
    · exact Or.inl (List.mem_append_right _ hl)
    · cases hl with
      | left h => exact Or.inr h
      | right h => exact Or.inl (List.mem_append_left _ (CapabilitySet.mem_ofList.mp h))
  | alloc _ ih =>
    refine .alloc (TraceOkFrom.congr ?_ ih)
    intro l' hl'
    simp only [List.mem_append, List.mem_cons] at hl' ⊢
    tauto

/-- Sequential composition of authorized traces: the second trace may use the
  allocations of the first. -/
theorem TraceOkFrom.append {R : CapabilitySet} {A : List Nat} {t1 t2 : Trace}
    (h1 : TraceOkFrom R A t1) (h2 : TraceOkFrom R (t1.allocList ++ A) t2) :
    TraceOkFrom R A (t1 ++ t2) := by
  induction h1 with
  | nil => simpa using h2
  | read hl _ ih => exact .read hl (ih (by simpa using h2))
  | access hl _ ih => exact .access hl (ih (by simpa using h2))
  | alloc _ ih =>
    refine .alloc (ih (TraceOkFrom.congr ?_ h2))
    intro l' hl'
    simp only [Trace.allocList_alloc, List.cons_append, List.mem_cons, List.mem_append] at hl' ⊢
    tauto

/-- Sequential composition for top-level authorization: the continuation's authority
  may include the head's allocations. -/
theorem TraceOk.append {R : CapabilitySet} {t1 t2 : Trace}
    (h1 : TraceOk t1 R) (h2 : TraceOk t2 (R ∪ CapabilitySet.ofList t1.allocList)) :
    TraceOk (t1 ++ t2) R :=
  TraceOkFrom.append h1 (by simpa using TraceOkFrom.of_auth (A := []) h2)

end CC
