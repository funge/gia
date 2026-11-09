import LinearEvaluator
import AuditPolicy

namespace GeneralizedIntervalArithmetic.QuadraticChordChecks

/-- Convex, concave, and affine cases use different sharp corrections. -/
theorem correction_cases :
    (∀ t ∈ Set.Icc (0:ℝ) 1, t - 1/4 ≤ t^2) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1, -t^2 ≤ -t + 1/4) := by
  constructor
  · have h := (quadratic_chord_lower_iff 0 0 1 (1/4)).2 (by norm_num)
    simpa using h
  · have h := (quadratic_chord_upper_iff 0 0 (-1) (-1/4)).2 (by norm_num)
    intro t ht
    have hh := h t ht
    nlinarith

theorem insufficient_correction :
    ¬ (∀ t ∈ Set.Icc (0:ℝ) 1, t - 1/8 ≤ t^2) := by
  intro h
  have hm := h (1/2) (by constructor <;> norm_num)
  norm_num at hm

theorem affine_zero_correction (p q : ℝ) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, (1-t)*p+t*(p+q) ≤ p+q*t) := by
  have h := (quadratic_chord_lower_iff p q 0 0).2 (by norm_num)
  simpa using h

/-- These bounds cannot be extrapolated outside the certified unit parameter. -/
theorem outside_unit_control : ¬ ((2:ℝ)^2 ≤ 2) := by norm_num

/-- A different-slope tangent is tighter at zero but looser at one: fixed-chord
optimality is not a universal greatest affine lower bound. -/
theorem incomparable_lower_bounds :
    (∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ t^2) ∧
    ((0:ℝ)-1/4 < 0) ∧ ((0:ℝ) < 1-1/4) := by
  exact ⟨fun _ _ => sq_nonneg _, by norm_num, by norm_num⟩

def coordinate : LinearInterval := .exact (QAffine.ofCoefficients 0 1)

theorem evaluator_square :
    evalLinear coordinate coordinate (.mul .x .x) =
      some (coordinate.mul coordinate) := rfl

theorem midpoint_value : Value (1/2) (1/2) (.mul .x .x) (1/4) := by
  have h : Value (1/2:ℝ) (1/2) (.mul .x .x) ((1/2)*(1/2)) := Value.mul Value.x Value.x
  norm_num at h
  exact h

theorem evaluator_enclosure :
    (coordinate.mul coordinate).Contains (1/2) (1/4) := by
  have hx : coordinate.Contains (1/2) (1/2) := by
    norm_num [coordinate,LinearInterval.Contains,LinearInterval.exact,
      QAffine.ofCoefficients,QAffine.value]
  exact evalLinear_sound (by norm_num) hx hx midpoint_value evaluator_square

theorem attained_lower_bound :
    ((coordinate.mul coordinate).lower.value (1/2)) = (1/4:ℝ) := by
  norm_num [coordinate,LinearInterval.mul,LinearInterval.join,QAffine.productBounds,
    QAffine.curvature,QAffine.ofCoefficients,LinearInterval.exact,QAffine.value]

theorem product_coefficients (t : ℝ) :
    (QAffine.ofCoefficients 2 3).value t * (QAffine.ofCoefficients (-1) 4).value t =
      -2+5*t+12*t^2 := by
  have h := affine_product_quadratic 2 3 (-1) 4 t
  norm_num at h
  exact h

end GeneralizedIntervalArithmetic.QuadraticChordChecks
#audit_namespace GeneralizedIntervalArithmetic.QuadraticChordChecks
