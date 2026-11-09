import Subdivision
import ConditionalArithmetic
import AuditPolicy

/- Fresh end-to-end regressions: no imports of milestone example fixtures. -/
namespace GeneralizedIntervalArithmetic.IntegrationChecks

def box : QInterval := ⟨-2,2,by norm_num⟩
def axis : QInterval := .point 0
def positive : Expr := .add (.mul .x .x) (.const 1)
def quotient : Expr := .div (.sub (.mul .x .x) (.const 2)) (.add .x (.const 3))

theorem initially_unknown : classifyBox exactBackend box axis positive = .unknown := by decide +kernel

theorem refined_empty : refineBox 1 exactBackend box axis positive = .empty := by decide +kernel

theorem refined_no_root : ¬ HasRoot box axis positive :=
  refineBox_empty exactBackend_sound refined_empty

theorem quotient_present : refineBox 1 exactBackend box axis quotient = .present := by decide +kernel

theorem quotient_defined_root : HasRoot box axis quotient :=
  refineBox_present exactBackend_sound quotient_present

theorem pole_unknown : refineBox 2 exactBackend box axis (.div (.const 1) .x) = .unknown := by
  decide +kernel

def X : LinearInterval := .exact ⟨0,1⟩
def Y : LinearInterval := .exact ⟨0,0⟩
def one : ConditionalExpr := .leaf (.const 1)
def two : ConditionalExpr := .leaf (.const 2)
def choice : ConditionalExpr := .iteLt .x (1/3) (.leaf (.const (-2))) (.leaf (.const 3))
def reciprocal : ConditionalExpr := arithmeticTree .div one choice

theorem composed_success : (evalConditionalArithmetic X Y .add reciprocal two).isSome := by
  decide +kernel

def result : LinearInterval :=
  (evalConditionalArithmetic X Y .add reciprocal two).get composed_success

theorem composed_coefficients : (result.lower,result.upper) = (⟨3/2,3/2⟩,⟨7/3,7/3⟩) := by
  decide +kernel

private theorem input_x (t : ℝ) : X.Contains t t := by
  apply (linear_exact_contains _ _ _).mpr
  simp [QAffine.value]
private theorem input_y (t : ℝ) : Y.Contains t 0 := by
  apply (linear_exact_contains _ _ _).mpr
  simp [QAffine.value]

theorem composed_defined {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃ z, ConditionalArithmeticValue t 0 .add reciprocal two z :=
  evalConditionalArithmetic_defined ht (input_x t) (input_y t)
    (Option.some_get composed_success).symm

theorem composed_excludes_zero {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ¬ ConditionalArithmeticValue t 0 .add reciprocal two 0 := by
  intro hv
  have h := evalConditionalArithmetic_sound ht (input_x t) (input_y t) hv
    (Option.some_get composed_success).symm
  have hl : result.lower = ⟨3/2,3/2⟩ := congrArg Prod.fst composed_coefficients
  have lower := h.1
  change result.lower.value t ≤ 0 at lower
  rw [hl] at lower
  norm_num [QAffine.value] at lower
  linarith

/-- Carry a real domain restriction through an actual interpreted expression. -/
def cancel : Expr := .add (.sub .x .x) (.const 3)
theorem cancel_success : (evalGuarded X Y cancel).isSome := by decide +kernel
def cancelResult : LinearInterval := (evalGuarded X Y cancel).get cancel_success

theorem restricted_contract :
    (cancelResult.partial.restrict (fun t : ℝ => 0 < t)).Sound
      (fun t z => 0 < t ∧ t ∈ Set.Icc (0:ℝ) 1 ∧ Value t 0 cancel z) :=
  evalGuarded_local_sound (fun t : ℝ => 0 < t)
    (fun t _ _ => input_x t) (fun t _ _ => input_y t)
    (Option.some_get cancel_success).symm

theorem restricted_absent_at_zero :
    ¬ ∃ z, (0 < (0:ℝ) ∧ (0:ℝ) ∈ Set.Icc 0 1 ∧ Value 0 0 cancel z) := by
  apply domain_absent restricted_contract
  simp [PartialEnclosure.restrict]

theorem restricted_interior_exists :
    ∃ z, 0 < (1/2:ℝ) ∧ (1/2:ℝ) ∈ Set.Icc 0 1 ∧ Value (1/2) 0 cancel z := by
  apply domain_definite restricted_contract
  change 0 < (1/2:ℝ) ∧ (1/2:ℝ) ∈ Set.Icc 0 1
  norm_num

end GeneralizedIntervalArithmetic.IntegrationChecks

#audit_namespace GeneralizedIntervalArithmetic.IntegrationChecks
