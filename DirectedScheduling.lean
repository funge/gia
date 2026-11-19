import HardwareAddition
import HardwareQuotientProgram

namespace GeneralizedIntervalArithmetic.DirectedScheduling
open HardwareAddition

inductive Direction where
  | down | up
  deriving DecidableEq, Repr

/-- Immutable inputs. Explicit direction also admits static-rounding backends. -/
structure Request (F : Type) where
  operation : HardwareQuotient.Operation
  direction : Direction
  left : F
  right : F

/-- Indexed phase results distinguish a skipped slot from an executed failure. -/
def phase {S F : Type} (denote : Request F → Option F) (requests : S → Request F)
    (direction : Direction) (slot : S) : Option (Option F) :=
  if (requests slot).direction = direction then some (denote (requests slot)) else none

/-- Stable slots, not phase positions, determine reconstruction. -/
def reassemble {S F : Type} (requests : S → Request F)
    (down up : S → Option (Option F)) (slot : S) : Option F :=
  match (requests slot).direction with
  | .down => (down slot).join
  | .up => (up slot).join

def scheduled {S F : Type} (denote : Request F → Option F) (requests : S → Request F) : S → Option F :=
  reassemble requests (phase denote requests .down) (phase denote requests .up)

/-- Exact same-denotation equivalence, including per-request None. No enclosure
contract implies this equality between independently chosen implementations. -/
theorem scheduled_eq {S F : Type} (denote : Request F → Option F) (requests : S → Request F) :
    scheduled denote requests = fun s => denote (requests s) := by
  funext s
  cases h : (requests s).direction <;> simp [scheduled,reassemble,phase,h]

/-- A concrete phase executor may discharge these same-outcome premises.
They are stronger than enclosure alone and are not asserted for native code here. -/
theorem reassemble_eq_of_outcomes {S F : Type} (denote : Request F → Option F)
    (requests : S → Request F) (down up : S → Option (Option F))
    (hd : ∀ s, (requests s).direction = .down → down s = some (denote (requests s)))
    (hu : ∀ s, (requests s).direction = .up → up s = some (denote (requests s))) :
    reassemble requests down up = fun s => denote (requests s) := by
  funext s
  cases h : (requests s).direction with
  | down => simp [reassemble,h,hd s h]
  | up => simp [reassemble,h,hu s h]

/-- A finite, sequential traversal writing outcomes to stable slots. -/
def execute {S F : Type} [DecidableEq S] (denote : Request F → Option F)
    (requests : S → Request F) : List S → (S → Option (Option F)) → S → Option (Option F)
  | [], out => out
  | s :: rest, out => execute denote requests rest
      (Function.update out s (some (denote (requests s))))

theorem execute_lookup {S F : Type} [DecidableEq S] (denote : Request F → Option F)
    (requests : S → Request F) (slots : List S) (out : S → Option (Option F)) (s : S) :
    execute denote requests slots out s = if s ∈ slots then some (denote (requests s)) else out s := by
  induction slots generalizing out with
  | nil => rfl
  | cons a rest ih =>
    rw [execute,ih]
    by_cases hr : s ∈ rest
    · simp [hr]
    · by_cases ha : s = a
      · subst a; simp [hr]
      · simp [hr,ha,Function.update_apply]

def groupedPhase {S F : Type} [DecidableEq S] (denote : Request F → Option F)
    (requests : S → Request F) (slots : List S) (direction : Direction) : S → Option (Option F) :=
  execute denote requests (slots.filter fun s => decide ((requests s).direction = direction)) (fun _ => none)

/-- Actual finite filtering/traversal realizes the abstract indexed phase. -/
theorem groupedPhase_eq {S F : Type} [DecidableEq S] (denote : Request F → Option F)
    (requests : S → Request F) (slots : List S) (complete : ∀ s, s ∈ slots) (direction : Direction) :
    groupedPhase denote requests slots direction = phase denote requests direction := by
  funext s
  simp [groupedPhase,execute_lookup,List.mem_filter,complete s,phase]

theorem grouped_reassembly_eq {S F : Type} [DecidableEq S] (denote : Request F → Option F)
    (requests : S → Request F) (slots : List S) (complete : ∀ s, s ∈ slots) :
    reassemble requests (groupedPhase denote requests slots .down)
      (groupedPhase denote requests slots .up) = fun s => denote (requests s) := by
  rw [groupedPhase_eq denote requests slots complete .down,
    groupedPhase_eq denote requests slots complete .up]
  exact scheduled_eq denote requests

inductive AddSlot where
  | lowerDown | lowerUp | upperDown | upperUp
  deriving DecidableEq, Repr

def addRequests {F : Type} (I J : Bounds F) : AddSlot → Request F
  | .lowerDown => ⟨.add,.down,I.lo,J.lo⟩
  | .lowerUp => ⟨.add,.up,I.lo,J.lo⟩
  | .upperDown => ⟨.add,.down,I.hi,J.hi⟩
  | .upperUp => ⟨.add,.up,I.hi,J.hi⟩

def pair {F : Type} (down up : Option F) : Option (F × F) := do
  let d ← down
  let u ← up
  return (d,u)

/-- Retain all four directed results, even the two not selected as endpoints. -/
def assembleSlots {F : Type} (results : AddSlot → Option F) : Option (Bounds F) :=
  assemble (pair (results .lowerDown) (results .lowerUp))
    (pair (results .upperDown) (results .upperUp))

def scalarAdd {F : Type} (denote : Request F → Option F) (I J : Bounds F) : Option (Bounds F) :=
  assembleSlots (fun s => denote (addRequests I J s))

def batchAdd {F : Type} (denote : Request F → Option F) (I J : Bounds F) : Option (Bounds F) :=
  assembleSlots (scheduled denote (addRequests I J))

theorem batchAdd_eq {F : Type} (denote : Request F → Option F) (I J : Bounds F) :
    batchAdd denote I J = scalarAdd denote I J := by
  simp only [batchAdd,scheduled_eq,scalarAdd]

theorem observed_add_eq {F : Type} (denote : Request F → Option F) (I J : Bounds F)
    (down up : AddSlot → Option (Option F))
    (hd : ∀ s, (addRequests I J s).direction = .down → down s = some (denote (addRequests I J s)))
    (hu : ∀ s, (addRequests I J s).direction = .up → up s = some (denote (addRequests I J s))) :
    assembleSlots (reassemble (addRequests I J) down up) = scalarAdd denote I J := by
  rw [reassemble_eq_of_outcomes denote (addRequests I J) down up hd hu]
  rfl

theorem grouped_add_eq {F : Type} (denote : Request F → Option F) (I J : Bounds F)
    (slots : List AddSlot) (complete : ∀ s, s ∈ slots) :
    assembleSlots (reassemble (addRequests I J)
      (groupedPhase denote (addRequests I J) slots .down)
      (groupedPhase denote (addRequests I J) slots .up)) = scalarAdd denote I J := by
  rw [grouped_reassembly_eq denote (addRequests I J) slots complete]
  rfl

theorem any_failure {F : Type} (results : AddSlot → Option F) (slot : AddSlot)
    (h : results slot = none) : assembleSlots results = none := by
  cases slot <;> simp [assembleSlots,pair,assemble,h]

/-- Existing observed-call contract, applied to the same paired outcomes. -/
theorem batchAdd_encloses {F : Type} {decode : F → Option ℝ}
    {denote : Request F → Option F} {I J R : Bounds F}
    (hl : CallSound decode I.lo J.lo
      (pair (denote (addRequests I J .lowerDown)) (denote (addRequests I J .lowerUp))))
    (hu : CallSound decode I.hi J.hi
      (pair (denote (addRequests I J .upperDown)) (denote (addRequests I J .upperUp))))
    (hr : batchAdd denote I J = some R)
    {x y : ℝ} (hx : Contains decode I x) (hy : Contains decode J y) : Contains decode R (x+y) := by
  rw [batchAdd_eq] at hr
  exact assemble_encloses hl hu hr hx hy

/-- Environmental failure is separate from request-level denotations. -/
def withEnvironment {F : Type} (ready : Bool) (denote : Request F → Option F)
    (I J : Bounds F) : Option (Bounds F) := if ready then batchAdd denote I J else none

theorem environment_failure {F : Type} (denote : Request F → Option F) (I J : Bounds F) :
    withEnvironment false denote I J = none := rfl

end GeneralizedIntervalArithmetic.DirectedScheduling
