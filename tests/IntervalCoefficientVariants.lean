import IntervalCoefficientVariants
import AuditPolicy
namespace GeneralizedIntervalArithmetic.IntervalCoefficientVariantsChecks
open IntervalCoefficientVariants

def unit : QInterval := ⟨0,1,by norm_num⟩
theorem attained (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (z : ℝ) :
    z ∈ values unit unit t ↔ 0 ≤ z ∧ z ≤ 1+t := by
  rw [exact_form unit unit ht.1]
  simp [form,LinearInterval.Contains,QAffine.ofCoefficients,QAffine.value,unit]
  intro _; constructor <;> intro h <;> nlinarith
theorem endpoints_and_interior :
    (1:ℝ) ∈ values unit unit 0 ∧ (3/2:ℝ) ∈ values unit unit (1/2) ∧
    (2:ℝ) ∈ values unit unit 1 := by
  constructor
  · rw [attained 0 (by norm_num)]; norm_num
  · constructor
    · rw [attained (1/2) (by norm_num)]; norm_num
    · rw [attained 1 (by norm_num)]; norm_num

theorem equal_interval_coefficients_not_singletons :
    (0:ℝ) ∈ values unit unit 1 ∧ (2:ℝ) ∈ values unit unit 1 := by
  constructor <;> rw [attained 1 (by norm_num)] <;> norm_num

theorem correlated_coefficients :
    (2:ℝ) ∈ values unit unit 1 ∧
    ¬ ∃ p q : ℝ, unit.Contains p ∧ unit.Contains q ∧ p+q=1 ∧ 2=p+q*1 := by
  constructor
  · exact endpoints_and_interior.2.2
  · rintro ⟨p,q,_,_,h,h'⟩; linarith

theorem negative_parameter_requires_other_bounds :
    (-1:ℝ) ∈ values unit unit (-1) ∧ ¬ (form unit unit).Contains (-1) (-1) := by
  constructor
  · rw [mem_values]; refine ⟨0,1,?_,?_,?_⟩ <;> norm_num [unit,QInterval.Contains]
  · norm_num [form,unit,LinearInterval.Contains,QAffine.value,QAffine.ofCoefficients]

theorem open_coefficients_do_not_attain_upper :
    ¬ ∃ p q : ℝ, p ∈ Set.Ioo (0:ℝ) 1 ∧ q ∈ Set.Ioo (0:ℝ) 1 ∧ 2=p+q := by
  rintro ⟨p,q,hp,hq,h⟩; linarith [hp.2,hq.2]

def point : QInterval := ⟨2,2,le_rfl⟩
theorem singleton_coefficients (t z : ℝ) :
    z ∈ values point point t ↔ z = 2+2*t := by
  rw [mem_values]
  constructor
  · rintro ⟨p,q,hp,hq,h⟩
    have hp' : p=2 := le_antisymm hp.2 hp.1
    have hq' : q=2 := le_antisymm hq.2 hq.1
    simpa [hp',hq'] using h
  · intro h
    exact ⟨2,2,⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩,h⟩
end GeneralizedIntervalArithmetic.IntervalCoefficientVariantsChecks
#audit_namespace GeneralizedIntervalArithmetic.IntervalCoefficientVariantsChecks
