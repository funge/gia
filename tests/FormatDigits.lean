import FormatDigits
import AuditPolicy
namespace GeneralizedIntervalArithmetic.FormatDigitsChecks
open FiniteFormat FormatDigits

def decimal : Format := ⟨10,2,0,0,by decide,by decide,by decide⟩
def twoExponents : Format := ⟨10,2,0,1,by decide,by decide,by decide⟩

theorem admitted_digits : Admitted decimal 99 ∧ ¬ Admitted decimal 100 := by
  norm_num [Admitted,decimal]

theorem leading_controls :
    9 / decimal.radix^(decimal.precision-1) = 0 ∧
    10 / decimal.radix^(decimal.precision-1) = 1 := by norm_num [decimal]

theorem boundary_normalization : ¬ Normalized decimal 9 ∧ Normalized decimal 10 ∧
    Normalized decimal 99 ∧ ¬ Normalized decimal 100 := by
  norm_num [Normalized,Admitted,decimal]

theorem packed_roundtrip : ∃ ds : List ℕ, ds.length ≤ 2 ∧
    (∀ d ∈ ds, d < 10) ∧ Nat.ofDigits 10 ds = 37 :=
  (digit_list decimal 37).mp (by norm_num [Admitted,decimal])

theorem one_tenth_literal : (1/10:ℚ) ∈ values decimal := by
  apply ((literal_nonnegative decimal (1/10)).mpr ?_).1
  exact ⟨1,0,by norm_num [decimal],by norm_num [decimal],by norm_num [decimal],
    by norm_num [eval,shift,decimal]⟩

theorem one_digit_not_literal : Repaired decimal 1 ∧ (1:ℚ) ∉ values decimal := by
  constructor
  · exact ⟨10,0,by norm_num [Admitted,decimal],by norm_num [decimal],by norm_num [decimal],
      Or.inl (by norm_num [eval,shift,decimal])⟩
  · intro h
    obtain ⟨n,e,hn,he,hf,hq⟩ := (literal_nonnegative decimal 1).mp ⟨h,by norm_num⟩
    have he0 : e=0 := by simp only [decimal] at he hf; omega
    have hh := literal_below decimal hn e
    rw [← hq,he0] at hh
    norm_num at hh

theorem minimum_control : NormalOrMinimum decimal 1 0 ∧
    ¬ ∃ k e, Normalized decimal k ∧ 0 ≤ e ∧ (1/10:ℚ)=eval decimal k e := by
  constructor
  · exact minimum_admitted decimal (by norm_num [Admitted,decimal])
  · simpa [decimal,eval,shift] using
      (minimum_not_normalizable decimal (n:=1) (by norm_num [decimal]))

/-- A leading-zero presentation above the minimum may normalize at a lower exponent. -/
theorem exponent_shift_control : eval twoExponents 1 1 = eval twoExponents 10 0 ∧
    Normalized twoExponents 10 := by
  norm_num [eval,shift,twoExponents,Normalized,Admitted]

/-- The printed digit display is unsigned; a sign closure is an explicit repair. -/
theorem negative_literal : (-(1/10):ℚ) ∈ values decimal ∧ Repaired decimal (-(1/10)) := by
  have hm : (-(1/10):ℚ) ∈ values decimal := by
    apply (mem_values decimal _).mpr
    exact ⟨-1,-1,by norm_num [bound,decimal],by norm_num [bound,decimal],
      by norm_num [shift,decimal],by norm_num [shift,decimal],by norm_num [value,decimal]⟩
  exact ⟨hm,literal_in_repaired decimal hm⟩

theorem negative_not_unsigned : ¬ ∃ n e, eval decimal n e = (-(1/10):ℚ) := by
  rintro ⟨n,e,h⟩
  have hh := eval_nonnegative decimal n e
  rw [h] at hh
  norm_num at hh

end GeneralizedIntervalArithmetic.FormatDigitsChecks
#audit_namespace GeneralizedIntervalArithmetic.FormatDigitsChecks
