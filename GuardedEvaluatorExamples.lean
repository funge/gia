import GuardedEvaluator
import LinearEvaluatorExamples
import DomainEvaluatorExamples

namespace GeneralizedIntervalArithmetic.GuardedEvaluatorExamples

def inputX : LinearInterval := .exact ⟨0,1⟩
def inputY : LinearInterval := .exact ⟨0,0⟩
def reciprocal : Expr := .div (.const 1) (.add (.const 1) .x)
def nestedReciprocal : Expr := .div (.const 1) reciprocal

def coefficients (e : Expr) : Option (QAffine × QAffine) :=
  (evalGuarded inputX inputY e).map (fun R => (R.lower,R.upper))

theorem reciprocal_coefficients : coefficients reciprocal = some (⟨1/2,1/2⟩,⟨1,1⟩) := by
  decide +kernel

theorem nested_coefficients : coefficients nestedReciprocal = some (⟨1,1⟩,⟨2,2⟩) := by
  decide +kernel

theorem quotient_retains_parameter :
    coefficients (.div .x (.add (.const 1) .x)) = some (⟨0,1/2⟩,⟨0,1⟩) := by
  decide +kernel

theorem safe_division_enabled : coefficients (.div (.const 1) (.const 1)) =
    some (⟨1,1⟩,⟨1,1⟩) := by decide +kernel

theorem boundary_pole_unknown : coefficients (.div (.const 1) .x) = none := by
  decide +kernel

theorem cancellation_denominator_unknown :
    coefficients (.div (.const 1) (.sub .x .x)) = none := by decide +kernel

theorem zero_times_pole_unknown :
    coefficients (.mul (.const 0) (.div (.const 1) (.const 0))) = none := by decide +kernel

theorem reciprocal_success : (evalGuarded inputX inputY reciprocal).isSome := by decide +kernel

def reciprocalResult : LinearInterval := (evalGuarded inputX inputY reciprocal).get reciprocal_success

theorem reciprocal_evaluation : evalGuarded inputX inputY reciprocal = some reciprocalResult :=
  (Option.some_get reciprocal_success).symm

/-- Independent semantic construction, not obtained from interpreter definedness. -/
theorem reciprocal_midpoint_value : Value (1/2:ℝ) 0 reciprocal (2/3) := by
  have h1 : Value (1/2:ℝ) 0 (.const 1) 1 := by
    simpa using (Value.const (x := (1/2:ℝ)) (y := 0) 1)
  have hx : Value (1/2:ℝ) 0 .x (1/2) := Value.x
  have hd : Value (1/2:ℝ) 0 (.add (.const 1) .x) (3/2) := by
    convert Value.add h1 hx using 1; norm_num
  convert Value.div h1 hd (by norm_num) using 1; norm_num [reciprocal]

/-- Failure on a box touching a pole does not erase defined interior values. -/
theorem unknown_has_defined_interior : Value (1/2:ℝ) 0 (.div (.const 1) .x) 2 := by
  have h1 : Value (1/2:ℝ) 0 (.const 1) 1 := by
    simpa using (Value.const (x := (1/2:ℝ)) (y := 0) 1)
  convert Value.div h1 (Value.x (x := (1/2:ℝ)) (y := 0)) (by norm_num) using 1; norm_num

theorem reciprocal_midpoint_enclosed : reciprocalResult.Contains (1/2) (2/3) := by
  apply evalGuarded_sound (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1) _ _
    reciprocal_midpoint_value reciprocal_evaluation
  · norm_num [inputX, LinearInterval.Contains, LinearInterval.exact, QAffine.value]
  · norm_num [inputY, LinearInterval.Contains, LinearInterval.exact, QAffine.value]

/-- Success on the certified input model does not prove global definedness. -/
theorem reciprocal_not_globally_defined : ¬ ∃ z, Value (-1:ℝ) 0 reciprocal z := by
  rintro ⟨z,hz⟩
  cases hz with
  | div hn hd hne =>
    cases hd with
    | add h1 hx =>
      cases h1
      cases hx
      norm_num at hne

theorem polynomial_result_preserved :
    evalGuarded LinearEvaluatorExamples.inputX LinearEvaluatorExamples.inputY
      LinearEvaluatorExamples.complementProduct = some LinearEvaluatorExamples.productResult :=
  evalGuarded_extends_polynomial LinearEvaluatorExamples.product_evaluation

theorem local_reciprocal_contract :
    (reciprocalResult.partial.restrict (fun t => t ≠ 0)).Sound
      (fun t z => t ≠ 0 ∧ t ∈ Set.Icc (0:ℝ) 1 ∧ Value t 0 reciprocal z) := by
  apply evalGuarded_local_sound (X := inputX) (Y := inputY) (fun t => t ≠ 0) _ _ reciprocal_evaluation
  · intro t _ _
    simp [inputX, LinearInterval.Contains, LinearInterval.exact, QAffine.value]
  · intro t _ _
    simp [inputY, LinearInterval.Contains, LinearInterval.exact, QAffine.value]

theorem punctured_success :
    (evalGuarded MultiplicationExamples.zero MultiplicationExamples.zero reciprocal).isSome := by
  decide +kernel

def puncturedResult : LinearInterval :=
  (evalGuarded MultiplicationExamples.zero MultiplicationExamples.zero reciprocal).get punctured_success

theorem punctured_contract :
    (puncturedResult.onDomain
      (MultiplicationExamples.punctured.inter MultiplicationExamples.everywhere)).Sound
      (ExpressionValues DomainEvaluatorExamples.PuncturedZero MultiplicationExamples.ZeroValue reciprocal) :=
  evalGuarded_relational_sound DomainEvaluatorExamples.punctured_zero_sound
    MultiplicationExamples.zero_domain_sound (Option.some_get punctured_success).symm

theorem punctured_environment_absent :
    ¬ ∃ z, ExpressionValues DomainEvaluatorExamples.PuncturedZero
      MultiplicationExamples.ZeroValue reciprocal 0 z := by
  apply domain_absent punctured_contract
  intro h
  exact h.2.1 rfl

theorem punctured_environment_defined :
    ∃ z, ExpressionValues DomainEvaluatorExamples.PuncturedZero
      MultiplicationExamples.ZeroValue reciprocal (1/2) z := by
  apply domain_definite punctured_contract
  change (1/2:ℝ) ∈ Set.Icc 0 1 ∧ (1/2:ℝ) ≠ 0 ∧ True
  norm_num

end GeneralizedIntervalArithmetic.GuardedEvaluatorExamples
