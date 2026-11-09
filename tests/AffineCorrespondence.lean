import LinearEvaluator
import AuditPolicy

namespace GeneralizedIntervalArithmetic.AffineCorrespondenceChecks

theorem negative_slope_endpoints : QAffine.ofCoefficients (1/2) (-3/2) = ⟨1/2,-1⟩ := by
  decide +kernel

theorem coefficient_realization : ∃ I : LinearInterval,
    I.lower = QAffine.ofCoefficients 1 (-2) ∧ I.upper = QAffine.ofCoefficients 3 (-1) := by
  apply (linear_coefficients_realizable_iff 1 (-2) 3 (-1)).mpr
  exact (affine_coefficients_order_iff 1 (-2) 3 (-1)).mpr (by norm_num)

/-- Agreement at one endpoint alone does not suffice. -/
theorem crossing_unrepresentable : ¬ ∃ I : LinearInterval,
    I.lower = QAffine.ofCoefficients 0 1 ∧ I.upper = QAffine.ofCoefficients 1 (-1) := by
  rw [linear_coefficients_realizable_iff,affine_coefficients_order_iff]
  norm_num

/-- The closed unit domain matters: valid affine bounds may cross outside it. -/
theorem outside_domain_control :
    (∀ t ∈ Set.Icc (0:ℝ) 1, (0:ℝ) ≤ 1-t) ∧ ¬ (0:ℝ) ≤ 1-2 := by
  constructor
  · intro t ht
    linarith [ht.2]
  · norm_num

/-- Endpoint testing is not a general test for nonlinear bounds. -/
theorem nonlinear_control :
    (0:ℝ) ≤ 0*(0-1) ∧ (0:ℝ) ≤ 1*(1-1) ∧ ¬ (0:ℝ) ≤ (1/2)*(1/2-1) := by
  norm_num

def X : LinearInterval := .exact (QAffine.ofCoefficients 0 1)
def Y : LinearInterval := .exact (QAffine.ofCoefficients 0 0)
def result : LinearInterval := X.sub X

theorem evaluator_result : evalLinear X Y (.sub .x .x) = some result := rfl

theorem computed_coefficients :
    (evalLinear X Y (.sub .x .x)).map (fun I => (I.lower.coefficients,I.upper.coefficients)) =
      some ((0,0),(0,0)) := by decide +kernel

theorem parameterized_input (t : ℝ) : X.Contains t t := by
  change (LinearInterval.exact (QAffine.ofCoefficients 0 1)).Contains t t
  rw [linear_exact_contains,affine_ofCoefficients_value]
  norm_num

theorem semantic_cancellation (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    result.Contains t 0 := by
  have hy : Y.Contains t 0 := by
    change (LinearInterval.exact (QAffine.ofCoefficients 0 0)).Contains t 0
    rw [linear_exact_contains,affine_ofCoefficients_value]
    norm_num
  have hv : Value t 0 (.sub .x .x) 0 := by
    simpa using (Value.sub (Value.x (x := t) (y := 0)) Value.x)
  exact evalLinear_sound ht (parameterized_input t) hy hv evaluator_result

theorem exact_zero_set (t z : ℝ) : result.Contains t z ↔ z = 0 :=
  linear_exact_cancel (QAffine.ofCoefficients 0 1) t z

/-- The ordinary constant-interval calculation in the same thesis example loses
shared dependence, yielding [-1,1] rather than a singleton. -/
def unit : QInterval := ⟨0,1,by norm_num⟩

theorem constant_comparison :
    ((unit.sub unit).lo,(unit.sub unit).hi) = (-1,1) := by decide +kernel

theorem nonexact_self_difference :
    ((LinearInterval.constant unit).sub (.constant unit)).Contains 0 1 := by
  norm_num [LinearInterval.Contains,LinearInterval.sub,LinearInterval.constant,
    QAffine.sub,QAffine.value,unit]

/-- Test coefficient containment on a nonconstant, non-singleton interval. -/
def band : LinearInterval :=
  ⟨QAffine.ofCoefficients 1 (-2),QAffine.ofCoefficients 3 (-1),by norm_num [QAffine.ofCoefficients],by norm_num [QAffine.ofCoefficients]⟩

theorem band_membership : band.Contains (1/2) 2 := by
  rw [linear_coefficients_contains]
  norm_num [band,QAffine.coefficients,QAffine.ofCoefficients]

end GeneralizedIntervalArithmetic.AffineCorrespondenceChecks
#audit_namespace GeneralizedIntervalArithmetic.AffineCorrespondenceChecks
