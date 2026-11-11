import SplitReduction
import AuditPolicy

namespace GeneralizedIntervalArithmetic.SplitReductionChecks
open HardwareAddition HardwareSine

def add (I J : Bounds Nat) : Option (Bounds Nat) := some ⟨I.lo+J.lo,I.hi+J.hi⟩
def mul (I J : Bounds Nat) : Option (Bounds Nat) := some ⟨I.lo*J.lo,I.hi*J.hi⟩
def sub (I J : Bounds Nat) : Option (Bounds Nat) := some ⟨I.lo-J.hi,I.hi-J.lo⟩

/-- Independent exact arithmetic exercises both accumulated corrections and the
final subtraction. These Nat test operations are not asserted to model FP. -/
theorem two_shifts : sweepSplit (m := Id) add mul sub (fun _ _ => true)
    (fun I => some I) ⟨3,3⟩ ⟨1,1⟩ [⟨4,4⟩,⟨2,2⟩] ⟨100,100⟩ ⟨0,0⟩ =
    some ⟨76,76⟩ := rfl

theorem skipped_shift : sweepSplit (m := Id) add mul sub (fun _ _ => false)
    (fun I => some I) ⟨3,3⟩ ⟨1,1⟩ [⟨4,4⟩] ⟨100,100⟩ ⟨2,2⟩ =
    some ⟨98,98⟩ := rfl

theorem correction_failure : sweepSplit (m := Id) (fun _ _ => none) mul sub
    (fun _ _ => true) (fun I => some I) ⟨3,3⟩ ⟨1,1⟩ [⟨4,4⟩]
    ⟨100,100⟩ ⟨0,0⟩ = none := rfl

theorem final_subtraction_failure : sweepSplit (m := Id) add mul (fun _ _ => none)
    (fun _ _ => false) (fun I => some I) ⟨3,3⟩ ⟨1,1⟩ []
    ⟨100,100⟩ ⟨0,0⟩ = none := rfl

theorem dropping_tail_unsound :
    ¬ Contains some (⟨HardwarePi.lower,HardwarePi.lower⟩ : Bounds ℝ) Real.pi :=
  HardwarePi.lower_singleton_misses

theorem tighter_width : HardwarePi.tailUpper-HardwarePi.tailLower <
    (HardwarePi.upper-HardwarePi.lower)/40000 := by
  have h := HardwarePi.tail_width.2
  rw [HardwarePi.width]
  norm_num at h ⊢
  linarith

end GeneralizedIntervalArithmetic.SplitReductionChecks
#audit_namespace GeneralizedIntervalArithmetic.SplitReductionChecks
