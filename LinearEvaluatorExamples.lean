import LinearEvaluator

namespace GeneralizedIntervalArithmetic.LinearEvaluatorExamples

def inputX : LinearInterval := .exact ⟨0, 1⟩
def inputY : LinearInterval := .exact ⟨1, 0⟩
def cancellation : Expr := .sub .x .x
def complementProduct : Expr := .mul .x (.sub (.const 1) .x)
def correlatedSum : Expr := .sub (.add .x .y) (.const 1)

def coefficients (e : Expr) : Option (QAffine × QAffine) :=
  (evalLinear inputX inputY e).map (fun I => (I.lower, I.upper))

theorem cancellation_coefficients : coefficients cancellation = some (⟨0,0⟩, ⟨0,0⟩) := by
  decide +kernel

theorem product_coefficients : coefficients complementProduct = some (⟨0,0⟩, ⟨1/4,1/4⟩) := by
  decide +kernel

theorem correlated_sum_coefficients : coefficients correlatedSum = some (⟨0,0⟩, ⟨0,0⟩) := by
  decide +kernel

theorem safe_division_unsupported : coefficients (.div (.const 1) (.const 1)) = none := by
  decide +kernel

theorem safe_division_has_value : Value (0:ℝ) 0 (.div (.const 1) (.const 1)) 1 := by
  convert Value.div (Value.const (x := (0:ℝ)) (y := 0) 1) (Value.const 1)
    (by norm_num) using 1; norm_num

theorem zero_times_pole_unsupported :
    coefficients (.mul (.const 0) (.div (.const 1) (.const 0))) = none := by decide +kernel

def productResult : LinearInterval := inputX.mul ((LinearInterval.exact ⟨1,1⟩).sub inputX)

theorem product_evaluation : evalLinear inputX inputY complementProduct = some productResult := rfl

theorem input_x_contains (t : ℝ) : inputX.Contains t t := by
  simp [inputX, LinearInterval.Contains, LinearInterval.exact, QAffine.value]

theorem input_y_contains (t : ℝ) : inputY.Contains t (1-t) := by
  simp [inputY, LinearInterval.Contains, LinearInterval.exact, QAffine.value]

theorem product_partial_sound : productResult.partial.Sound
    (fun t z => t ∈ Set.Icc (0:ℝ) 1 ∧ Value t (1-t) complementProduct z) :=
  evalLinear_partial_sound (fun t _ => input_x_contains t)
    (fun t _ => input_y_contains t) product_evaluation

theorem product_semantics_enclosed {t z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hv : Value t (1-t) complementProduct z) : productResult.Contains t z :=
  evalLinear_sound ht (input_x_contains t) (input_y_contains t) hv product_evaluation

theorem product_semantics_exists (t : ℝ) : ∃ z, Value t (1-t) complementProduct z :=
  evalLinear_defined product_evaluation t (1-t)

theorem restricted_product_sound : (productResult.partial.restrict (fun t => t ≠ 0)).Sound
    (fun t z => t ≠ 0 ∧ t ∈ Set.Icc (0:ℝ) 1 ∧ Value t (1-t) complementProduct z) :=
  evalLinear_restricted_sound (fun t _ => input_x_contains t)
    (fun t _ => input_y_contains t) product_evaluation _

end GeneralizedIntervalArithmetic.LinearEvaluatorExamples
