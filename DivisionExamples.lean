import LinearDivision
import MultiplicationExamples

namespace GeneralizedIntervalArithmetic.DivisionExamples

def numerator : LinearInterval := .exact ⟨0,1⟩
def denominator : LinearInterval := .exact ⟨1,2⟩
def negativeDenominator : LinearInterval := .exact ⟨-2,-1⟩
def one : LinearInterval := .exact ⟨1,1⟩
def zero : LinearInterval := .exact ⟨0,0⟩
def crossing : LinearInterval := .constant ⟨-1,1,by norm_num⟩

def coefficients (I : Option LinearInterval) : Option (QAffine × QAffine) :=
  I.map (fun R => (R.lower, R.upper))

theorem reciprocal_positive : coefficients denominator.recip? = some (⟨1/2,1/2⟩,⟨1,1⟩) := by
  decide +kernel

theorem reciprocal_negative : coefficients negativeDenominator.recip? = some (⟨-1,-1⟩,⟨-1/2,-1/2⟩) := by
  decide +kernel

theorem quotient_retains_numerator : coefficients (numerator.div? denominator) =
    some (⟨0,1/2⟩,⟨0,1⟩) := by decide +kernel

theorem constant_division_exact : coefficients (one.div? one) = some (⟨1,1⟩,⟨1,1⟩) := by
  decide +kernel

theorem zero_denominator_unknown : coefficients (one.div? zero) = none := by decide +kernel

theorem crossing_denominator_unknown : coefficients (one.div? crossing) = none := by decide +kernel

theorem boundary_denominator_unknown : coefficients (one.div? numerator) = none := by decide +kernel

theorem zero_numerator_does_not_bypass_guard : coefficients (zero.div? crossing) = none := by
  decide +kernel

/-- A failed guard can coexist with a defined denominator value at every parameter. -/
theorem unknown_denominator_can_enclose_one (t : ℝ) : crossing.Contains t 1 :=
  (linear_constant_contains _ _ _).mpr (by norm_num [QInterval.Contains])

theorem one_over_one_defined : QuotientValues (fun _ z : ℝ => z = 1)
    (fun _ z : ℝ => z = 1) 0 1 := by
  exact ⟨1,1,rfl,rfl,by norm_num,by norm_num⟩

/-- A successful guard retains both operand domain descriptions. -/
theorem punctured_quotient_sound :
    (MultiplicationExamples.zero.onDomain
      (MultiplicationExamples.everywhere.inter MultiplicationExamples.punctured)).Sound
      (QuotientValues MultiplicationExamples.ZeroValue MultiplicationExamples.PuncturedOneValue) :=
  linear_div_domain_sound MultiplicationExamples.zero_domain_sound
    MultiplicationExamples.punctured_one_sound (by
      norm_num [LinearInterval.div?, LinearInterval.recip?, LinearInterval.hull,
        QInterval.AwayZero, QInterval.recip, LinearInterval.constant, LinearInterval.mul,
        LinearInterval.join, QAffine.productBounds, QAffine.curvature,
        MultiplicationExamples.zero, MultiplicationExamples.one, LinearInterval.exact])

theorem punctured_quotient_absent_at_zero :
    ¬ ∃ z, QuotientValues MultiplicationExamples.ZeroValue
      MultiplicationExamples.PuncturedOneValue 0 z := by
  apply domain_absent punctured_quotient_sound
  intro h
  exact h.2.2 rfl

end GeneralizedIntervalArithmetic.DivisionExamples
