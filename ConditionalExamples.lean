import ConditionalEvaluator
import PiecewiseExamples
import DomainEvaluatorExamples
import GuardedEvaluatorExamples

namespace GeneralizedIntervalArithmetic.ConditionalExamples

def inputX : LinearInterval := .exact ⟨0,1⟩
def inputY : LinearInterval := .exact ⟨0,0⟩
def pole : Expr := .div (.const 1) (.const 0)
def seven : ConditionalExpr := .leaf (.const 7)
def nine : ConditionalExpr := .leaf (.const 9)
def bad : ConditionalExpr := .leaf pole
def chooseTrue : ConditionalExpr := .iteLt (.const 0) 1 seven bad
def chooseFalse : ConditionalExpr := .iteLt (.const 1) 1 bad nine
def chooseBad : ConditionalExpr := .iteLt (.const 0) 1 bad seven
def badGuard : ConditionalExpr := .iteLt pole 0 seven seven
def unresolvedPartial : ConditionalExpr := .iteLt .x (1/2) seven bad
def jumpTree : ConditionalExpr := .iteLt .x (1/2) (.leaf (.const (-1))) (.leaf (.const 1))
def nested : ConditionalExpr := .iteLt (.const 0) 1 chooseFalse badGuard
def partialGuardTree : ConditionalExpr :=
  .iteLt GuardedEvaluatorExamples.reciprocal 2 seven bad

def coefficients (e : ConditionalExpr) : Option (QAffine × QAffine) :=
  (evalConditional inputX inputY e).map (fun R => (R.lower,R.upper))

theorem true_skips_pole : coefficients chooseTrue = some (⟨7,7⟩,⟨7,7⟩) := by decide +kernel

theorem equality_false_skips_pole : coefficients chooseFalse = some (⟨9,9⟩,⟨9,9⟩) := by decide +kernel

theorem active_pole_unknown : coefficients chooseBad = none := by decide +kernel

theorem undefined_guard_unknown : coefficients badGuard = none := by decide +kernel

theorem unresolved_partial_unknown : coefficients unresolvedPartial = none := by decide +kernel

theorem unresolved_total_join : coefficients jumpTree = some (⟨-1,-1⟩,⟨1,1⟩) := by decide +kernel

theorem nested_skips_bad_guard : coefficients nested = some (⟨9,9⟩,⟨9,9⟩) := by decide +kernel

theorem locally_defined_guard_skips_pole :
    coefficients partialGuardTree = some (⟨7,7⟩,⟨7,7⟩) := by decide +kernel

theorem partial_guard_not_global : ¬ ∃ z, ConditionalValue (-1) 0 partialGuardTree z := by
  rintro ⟨z,h⟩
  cases h with
  | yes hg _ _ => exact GuardedEvaluatorExamples.reciprocal_not_globally_defined ⟨_,hg⟩
  | no hg _ _ => exact GuardedEvaluatorExamples.reciprocal_not_globally_defined ⟨_,hg⟩

theorem pole_has_no_value (x y : ℝ) : ¬ ∃ z, Value x y pole z := by
  rintro ⟨z,h⟩
  cases h with
  | div ha hb hn =>
    cases hb
    norm_num at hn

theorem seven_value (x y : ℝ) : ConditionalValue x y seven 7 := by
  apply ConditionalValue.leaf
  simpa using (Value.const (x := x) (y := y) 7)

/-- Direct semantic proof: the inactive pole has no required Value premise. -/
theorem choose_true_value (x y : ℝ) : ConditionalValue x y chooseTrue 7 := by
  have h0 : Value x y (.const 0) 0 := by simpa using (Value.const (x := x) (y := y) 0)
  exact ConditionalValue.yes h0 (by norm_num) (seven_value x y)

theorem choose_false_value (x y : ℝ) : ConditionalValue x y chooseFalse 9 := by
  have h1 : Value x y (.const 1) 1 := by simpa using (Value.const (x := x) (y := y) 1)
  have h9 : ConditionalValue x y nine 9 := by
    apply ConditionalValue.leaf
    simpa using (Value.const (x := x) (y := y) 9)
  exact ConditionalValue.no h1 (by norm_num) h9

theorem undefined_guard_no_value (x y : ℝ) : ¬ ∃ z, ConditionalValue x y badGuard z := by
  rintro ⟨z,h⟩
  cases h with
  | yes hg _ _ => exact pole_has_no_value x y ⟨_,hg⟩
  | no hg _ _ => exact pole_has_no_value x y ⟨_,hg⟩

theorem active_pole_no_value (x y : ℝ) : ¬ ∃ z, ConditionalValue x y chooseBad z := by
  rintro ⟨z,h⟩
  cases h with
  | yes _ _ hb =>
    cases hb with
    | leaf hv => exact pole_has_no_value x y ⟨_,hv⟩
  | no hg hle _ =>
    cases hg
    norm_num at hle

theorem unresolved_has_defined_point : ConditionalValue 0 0 unresolvedPartial 7 :=
  ConditionalValue.yes Value.x (by norm_num) (seven_value 0 0)

theorem unresolved_has_undefined_point : ¬ ∃ z, ConditionalValue 1 0 unresolvedPartial z := by
  rintro ⟨z,h⟩
  cases h with
  | yes hg hlt _ =>
    cases hg
    norm_num at hlt
  | no _ _ hb =>
    cases hb with
    | leaf hv => exact pole_has_no_value 1 0 ⟨_,hv⟩

theorem jump_semantic_value (t : ℝ) : ConditionalValue t 0 jumpTree (PiecewiseExamples.jump t) := by
  unfold PiecewiseExamples.jump
  split
  · rename_i ht
    apply ConditionalValue.yes (u := t) Value.x (by simpa using ht)
    apply ConditionalValue.leaf
    simpa using (Value.const (x := t) (y := (0:ℝ)) (-1))
  · rename_i ht
    apply ConditionalValue.no (u := t) Value.x (by simpa using le_of_not_gt ht)
    apply ConditionalValue.leaf
    simpa using (Value.const (x := t) (y := (0:ℝ)) 1)

theorem interpreted_jump_not_continuous :
    ¬ ContinuousOn PiecewiseExamples.jump (Set.Icc (0:ℝ) 1) :=
  PiecewiseExamples.jump_not_continuous

theorem punctured_success :
    (evalConditional MultiplicationExamples.zero MultiplicationExamples.zero chooseTrue).isSome := by
  decide +kernel

def puncturedResult : LinearInterval :=
  (evalConditional MultiplicationExamples.zero MultiplicationExamples.zero chooseTrue).get punctured_success

theorem punctured_contract :
    (puncturedResult.onDomain
      (MultiplicationExamples.punctured.inter MultiplicationExamples.everywhere)).Sound
      (ConditionalExpressionValues DomainEvaluatorExamples.PuncturedZero
        MultiplicationExamples.ZeroValue chooseTrue) :=
  evalConditional_relational_sound DomainEvaluatorExamples.punctured_zero_sound
    MultiplicationExamples.zero_domain_sound (Option.some_get punctured_success).symm

theorem punctured_environment_absent :
    ¬ ∃ z, ConditionalExpressionValues DomainEvaluatorExamples.PuncturedZero
      MultiplicationExamples.ZeroValue chooseTrue 0 z := by
  apply domain_absent punctured_contract
  intro h
  exact h.2.1 rfl

theorem punctured_environment_defined :
    ∃ z, ConditionalExpressionValues DomainEvaluatorExamples.PuncturedZero
      MultiplicationExamples.ZeroValue chooseTrue (1/2) z := by
  apply domain_definite punctured_contract
  change (1/2:ℝ) ∈ Set.Icc 0 1 ∧ (1/2:ℝ) ≠ 0 ∧ True
  norm_num

end GeneralizedIntervalArithmetic.ConditionalExamples
