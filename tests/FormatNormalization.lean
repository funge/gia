import FormatNormalization
import AuditPolicy
namespace GeneralizedIntervalArithmetic.FormatNormalizationChecks
open FiniteFormat FormatDigits FormatNormalization

def decimal : Format := ⟨10,3,-3,4,by norm_num,by norm_num,by norm_num⟩
def oneDigit : Format := ⟨3,1,-2,2,by norm_num,by norm_num,by norm_num⟩
def negativeRange : Format := ⟨2,3,-4,-2,by norm_num,by norm_num,by norm_num⟩
def singletonRange : Format := ⟨5,2,0,0,by norm_num,by norm_num,by norm_num⟩

theorem decimal_witness : (10000:ℚ) ∉ values decimal ∧ Repaired decimal 10000 := by
  constructor
  · have h := (upper_digit_witness decimal).2.2.2
    have he : (decimal.radix:ℚ)^decimal.maxExponent = 10000 := by norm_num [decimal]
    rw [he] at h; exact h
  · exact ⟨100,4,by norm_num [Admitted,decimal],by norm_num [decimal],le_rfl,
      Or.inl (by norm_num [eval,shift,decimal])⟩

theorem precision_one : (9:ℚ) ∉ values oneDigit ∧ Normalized oneDigit 1 := by
  have h := (upper_digit_witness oneDigit).2.2.2
  have he : (oneDigit.radix:ℚ)^oneDigit.maxExponent = 9 := by norm_num [oneDigit]
  rw [he] at h
  exact ⟨h,by norm_num [Normalized,Admitted,oneDigit]⟩

theorem negative_exponent_witness : (1/4:ℚ) ∉ values negativeRange := by
  have h := (upper_digit_witness negativeRange).2.2.2
  have he : (negativeRange.radix:ℚ)^negativeRange.maxExponent = 1/4 := by norm_num [negativeRange]
  rw [he] at h; exact h

theorem singleton_exponents : (1:ℚ) ∉ values singletonRange := by
  have h := (upper_digit_witness singletonRange).2.2.2
  have he : (singletonRange.radix:ℚ)^singletonRange.maxExponent = 1 := by norm_num [singletonRange]
  rw [he] at h; exact h

/-- Two shifts are needed, not just one local exponent identity. -/
theorem multiple_shifts : eval decimal 1 2 = eval decimal 100 0 ∧
    NormalOrMinimum decimal 100 0 := by
  norm_num [eval,shift,NormalOrMinimum,Admitted,decimal]

theorem negative_preserved : ∃ n e, NormalOrMinimum decimal n e ∧
    (-1:ℚ) = -eval decimal n e := by
  exact ⟨100,0,multiple_shifts.2,by norm_num [eval,shift,decimal]⟩

theorem zero_stops : NormalOrMinimum decimal 0 (-3) ∧ eval decimal 0 (-3) = 0 := by
  exact ⟨minimum_admitted decimal (by norm_num [Admitted,decimal]),by simp [eval]⟩

theorem bottom_denormal : NormalOrMinimum decimal 1 (-3) ∧
    ¬ ∃ k e, Normalized decimal k ∧ decimal.minExponent ≤ e ∧
      eval decimal 1 decimal.minExponent = eval decimal k e := by
  exact ⟨minimum_admitted decimal (by norm_num [Admitted,decimal]),
    minimum_not_normalizable decimal (by norm_num [decimal])⟩

/-- Equality of sets is not equality of the original presentations. -/
theorem representation_changes : ¬ NormalOrMinimum decimal 1 2 ∧
    ∃ n e, NormalOrMinimum decimal n e ∧ eval decimal 1 2 = eval decimal n e := by
  refine ⟨by norm_num [NormalOrMinimum,Admitted,decimal],?_⟩
  exact normalize decimal (by norm_num [Admitted,decimal]) (by norm_num [decimal]) (by norm_num [decimal])

end GeneralizedIntervalArithmetic.FormatNormalizationChecks
#audit_namespace GeneralizedIntervalArithmetic.FormatNormalizationChecks
