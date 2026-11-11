import DyadicReduction
import AuditPolicy

namespace GeneralizedIntervalArithmetic.DyadicReductionChecks
open HardwareAddition HardwareSine

def addNat (I J : Bounds Nat) : Option (Bounds Nat) := some ⟨I.lo+J.lo,I.hi+J.hi⟩

theorem generated : doubledPeriods (m := Id) addNat 3 ⟨2,2⟩ =
    some [⟨2,2⟩,⟨4,4⟩,⟨8,8⟩] := rfl

theorem generation_failure : doubledPeriods (m := Id) (fun _ _ => none)
    3 (⟨2,2⟩ : Bounds Nat) = none := rfl

theorem reject_shift : sweepPeriods (m := Id) (fun C _ => some C)
    (fun _ _ => none) (fun _ _ => false) (fun I => some I)
    (⟨0,0⟩ : Bounds Nat) [⟨2,2⟩] ⟨7,8⟩ = some ⟨7,8⟩ := rfl

theorem accepted_failure : sweepPeriods (m := Id) (fun C _ => some C)
    (fun _ _ => none) (fun _ _ => true) (fun I => some I)
    (⟨0,0⟩ : Bounds Nat) [⟨2,2⟩] ⟨7,8⟩ = none := rfl

/-- The selector need not be a mathematically correct quotient estimator.
Even accepting a deliberately unhelpful period preserves the sine value. -/
theorem unhelpful_period (x : ℝ) : Real.sin (x - (100:ℝ)*(2*Real.pi)) = Real.sin x := by
  simpa using Real.sin_sub_int_mul_two_pi x (100 : ℤ)

end GeneralizedIntervalArithmetic.DyadicReductionChecks
#audit_namespace GeneralizedIntervalArithmetic.DyadicReductionChecks
