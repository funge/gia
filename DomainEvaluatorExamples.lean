import DomainEvaluator
import MultiplicationExamples

namespace GeneralizedIntervalArithmetic.DomainEvaluatorExamples
open MultiplicationExamples

def PuncturedZero (t z : ℝ) : Prop := t ∈ Set.Icc (0:ℝ) 1 ∧ t ≠ 0 ∧ z = 0

theorem punctured_zero_sound : (zero.onDomain punctured).Sound PuncturedZero := by
  refine ⟨?_, fun _ _ h => ⟨h.1,h.2.1⟩, fun t h => ⟨0,h.1,h.2,rfl⟩⟩
  rintro t z ⟨_,_,rfl⟩
  simp [LinearInterval.onDomain, FunctionalBounds.Contains, zero,
    LinearInterval.exact, QAffine.value]

def cancellation : Expr := .sub .x .x
def result : LinearInterval := zero.sub zero

theorem partial_cancellation_sound :
    (result.onDomain (punctured.inter everywhere)).Sound
      (ExpressionValues PuncturedZero ZeroValue cancellation) :=
  evalLinear_relational_sound punctured_zero_sound zero_domain_sound (by rfl)

theorem partial_cancellation_absent :
    ¬ ∃ z, ExpressionValues PuncturedZero ZeroValue cancellation 0 z := by
  apply domain_absent partial_cancellation_sound
  intro h
  exact h.2.1 rfl

theorem partial_cancellation_defined :
    ∃ z, ExpressionValues PuncturedZero ZeroValue cancellation (1/2) z := by
  apply domain_definite partial_cancellation_sound
  change (1/2:ℝ) ∈ Set.Icc 0 1 ∧ (1/2:ℝ) ≠ 0 ∧ True
  norm_num

/-- Arbitrary values outside the intended domain are irrelevant to local enclosure. -/
noncomputable def representative (t : ℝ) : ℝ := if t = 0 then 7 else 0

theorem representative_not_globally_enclosed : ¬ zero.Contains 0 (representative 0) := by
  norm_num [zero, representative, LinearInterval.Contains, LinearInterval.exact, QAffine.value]

theorem representative_locally_enclosed {t : ℝ} (ht : t ≠ 0) :
    zero.Contains t (representative t) := by
  simp [representative, ht, zero, LinearInterval.Contains, LinearInterval.exact, QAffine.value]

theorem local_function_bridge : (zero.partial.restrict (fun t => t ≠ 0)).Sound
    (fun t z => t ≠ 0 ∧ t ∈ Set.Icc (0:ℝ) 1 ∧ Value (representative t) 0 .x z) := by
  apply evalLinear_local_sound (X := zero) (Y := zero) (e := .x) (fun t => t ≠ 0)
  · intro t _ ht
    exact representative_locally_enclosed ht
  · intro t _ _
    simp [zero, LinearInterval.Contains, LinearInterval.exact, QAffine.value]
  · rfl

def uncertain : DomainBounds ℝ := ⟨fun _ => False, fun _ => True, fun _ h => h.elim⟩

theorem empty_coordinate_sound : (zero.onDomain uncertain).Sound (fun _ _ => False) := by
  exact ⟨fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ h => h.2.elim⟩

theorem unknown_result_sound : (result.onDomain (uncertain.inter everywhere)).Sound
    (ExpressionValues (fun _ _ => False) ZeroValue cancellation) :=
  evalLinear_relational_sound empty_coordinate_sound zero_domain_sound (by rfl)

theorem unknown_result_domain :
    (result.onDomain (uncertain.inter everywhere)).domain.possible (1/2) ∧
    ¬ (result.onDomain (uncertain.inter everywhere)).domain.definite (1/2) := by
  norm_num [LinearInterval.onDomain, DomainBounds.inter, uncertain, everywhere]

theorem unknown_environment_has_no_values :
    ¬ ∃ z, ExpressionValues (fun _ _ => False) ZeroValue cancellation (1/2) z := by
  rintro ⟨z,x,y,hx,_,_⟩
  exact hx

end GeneralizedIntervalArithmetic.DomainEvaluatorExamples
