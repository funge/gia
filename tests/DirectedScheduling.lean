import DirectedScheduling
import AuditPolicy

namespace GeneralizedIntervalArithmetic.DirectedSchedulingChecks
open DirectedScheduling HardwareAddition

def arithmetic (r : Request Nat) : Option Nat :=
  match r.operation with
  | .add => some (r.left+r.right)
  | .sub => some (r.left-r.right)
  | .mul => some (r.left*r.right)
  | .div => if r.right=0 then none else some (r.left/r.right)

def mixed : AddSlot → Request Nat
  | .lowerDown => ⟨.add,.up,2,3⟩
  | .lowerUp => ⟨.sub,.down,8,3⟩
  | .upperDown => ⟨.mul,.up,4,5⟩
  | .upperUp => ⟨.div,.down,7,0⟩

theorem four_opcodes : scheduled arithmetic mixed .lowerDown = some 5 ∧
    scheduled arithmetic mixed .lowerUp = some 5 ∧
    scheduled arithmetic mixed .upperDown = some 20 ∧
    scheduled arithmetic mixed .upperUp = none := by
  simp [scheduled_eq,arithmetic,mixed]

theorem skipped_vs_failed : phase arithmetic mixed .down .upperUp = some none ∧
    phase arithmetic mixed .up .upperUp = none := by constructor <;> rfl

-- Each failure survives assembly, including lower-Up and upper-Down.
theorem four_failure_slots (slot : AddSlot) :
    assembleSlots (fun s => if s=slot then none else some (5:Nat)) = none :=
  any_failure _ slot (by simp)

theorem add_result : (batchAdd arithmetic ⟨1,2⟩ ⟨3,4⟩).map (fun b => (b.lo,b.hi)) = some (4,6) := by
  simp [batchAdd_eq,scalarAdd,assembleSlots,pair,assemble,arithmetic,addRequests]

theorem environmental_failure_not_scalar_equality :
    withEnvironment false arithmetic ⟨1,2⟩ ⟨3,4⟩ = none ∧
    scalarAdd arithmetic ⟨1,2⟩ ⟨3,4⟩ ≠ none := by
  simp [withEnvironment,scalarAdd,assembleSlots,pair,assemble,arithmetic,addRequests]

-- Stage two is constructed only after stage one's immutable request returns.
def dependentRun : Option Nat := do
  let x ← scheduled arithmetic (fun _ : Unit => ⟨.add,.down,1,2⟩) ()
  scheduled arithmetic (fun _ : Unit => ⟨.add,.up,x,4⟩) ()

theorem dependency_boundary : dependentRun = some 7 ∧
    scheduled arithmetic (fun _ : Unit => ⟨.add,.up,0,4⟩) () = some 4 := by
  simp [dependentRun,scheduled_eq,arithmetic]

def failedDependency : Option Nat := do
  let x ← scheduled arithmetic (fun _ : Unit => ⟨.div,.down,1,0⟩) ()
  scheduled arithmetic (fun _ : Unit => ⟨.add,.up,x,4⟩) ()

theorem dependency_failure : failedDependency = none := by
  simp [failedDependency,scheduled_eq,arithmetic]

-- Enclosure alone does not force even real equality, hence cannot force bit equality.
theorem sound_not_equal : CallSound some (0:ℝ) 0 (some (0,0)) ∧
    CallSound some (0:ℝ) 0 (some (-1,1)) ∧
    (some ((0:ℝ),0) : Option (ℝ×ℝ)) ≠ some (-1,1) := by
  refine ⟨?_,?_,?_⟩
  · norm_num [CallSound]
  · norm_num [CallSound]
  · intro h
    have hfirst := congrArg Prod.fst (Option.some.inj h)
    norm_num at hfirst

theorem sound_allows_failure : CallSound some (0:ℝ) 0 none := by simp [CallSound]

#audit_namespace GeneralizedIntervalArithmetic.DirectedSchedulingChecks
end GeneralizedIntervalArithmetic.DirectedSchedulingChecks
