import ConditionalArithmetic
import ConditionalExamples

namespace GeneralizedIntervalArithmetic.ConditionalArithmeticExamples

open ConditionalExamples

def coefficients (op : ArithmeticOp) (a b : ConditionalExpr) : Option (QAffine × QAffine) :=
  (evalConditionalArithmetic inputX inputY op a b).map (fun R => (R.lower,R.upper))

def one : ConditionalExpr := .leaf (.const 1)
def zero : ConditionalExpr := .leaf (.const 0)

theorem add_two_choices : coefficients .add chooseTrue chooseFalse = some (⟨16,16⟩,⟨16,16⟩) := by
  decide +kernel

theorem subtract_two_choices : coefficients .sub chooseTrue chooseFalse = some (⟨-2,-2⟩,⟨-2,-2⟩) := by
  decide +kernel

theorem multiply_two_choices : coefficients .mul chooseTrue chooseFalse = some (⟨63,63⟩,⟨63,63⟩) := by
  decide +kernel

theorem divide_two_choices : coefficients .div chooseTrue chooseFalse = some (⟨7/9,7/9⟩,⟨7/9,7/9⟩) := by
  decide +kernel

/-- Semantic witnesses come from the operands, independently of interval evaluation. -/
theorem division_value (x y : ℝ) : ConditionalArithmeticValue x y .div chooseTrue chooseFalse (7/9) := by
  refine ⟨7,9,choose_true_value x y,choose_false_value x y,?_⟩
  change (9:ℝ) ≠ 0 ∧ (7/9:ℝ) = 7/9
  norm_num

theorem zero_times_bad_unknown : coefficients .mul zero bad = none := by decide +kernel

theorem bad_times_zero_unknown : coefficients .mul bad zero = none := by decide +kernel

theorem zero_times_bad_no_value (x y : ℝ) :
    ¬ ∃ z, ConditionalValue x y (arithmeticTree .mul zero bad) z := by
  rintro ⟨z,h⟩
  obtain ⟨u,v,_,hv,_⟩ := (arithmeticTree_value_iff x y .mul zero bad z).mp h
  cases hv with
  | leaf hv => exact pole_has_no_value x y ⟨v,hv⟩

theorem bad_times_zero_no_value (x y : ℝ) :
    ¬ ∃ z, ConditionalValue x y (arithmeticTree .mul bad zero) z := by
  rintro ⟨z,h⟩
  obtain ⟨u,v,hu,_,_⟩ := (arithmeticTree_value_iff x y .mul bad zero z).mp h
  cases hu with
  | leaf hu => exact pole_has_no_value x y ⟨u,hu⟩

theorem divide_by_zero_unknown : coefficients .div chooseTrue zero = none := by decide +kernel

theorem divide_by_zero_no_value (x y : ℝ) :
    ¬ ∃ z, ConditionalValue x y (arithmeticTree .div chooseTrue zero) z := by
  rintro ⟨z,h⟩
  obtain ⟨u,v,_,hv,hn,_⟩ := (arithmeticTree_value_iff x y .div chooseTrue zero z).mp h
  cases hv with
  | leaf hv => cases hv; norm_num at hn

/-- Branch-local division succeeds even though joining the denominator first loses the sign. -/
theorem reciprocal_jump_enclosed : coefficients .div one jumpTree = some (⟨-1,-1⟩,⟨1,1⟩) := by
  decide +kernel

theorem joined_denominator_unknown :
    ((evalConditional inputX inputY one).bind fun I =>
      (evalConditional inputX inputY jumpTree).bind fun J => I.div? J).isNone = true := by
  decide +kernel

theorem one_value (x y : ℝ) : ConditionalValue x y one 1 := by
  apply ConditionalValue.leaf
  simpa using (Value.const (x := x) (y := y) 1)

theorem reciprocal_jump_value (t : ℝ) :
    ConditionalArithmeticValue t 0 .div one jumpTree (1 / PiecewiseExamples.jump t) := by
  refine ⟨1,PiecewiseExamples.jump t,one_value t 0,jump_semantic_value t,?_,rfl⟩
  unfold PiecewiseExamples.jump
  split <;> norm_num

/-- Both occurrences use the same coordinates semantically, but compilation does
not prune inconsistent combinations of unresolved guard decisions. -/
def cancelJump : ConditionalExpr := arithmeticTree .sub jumpTree jumpTree
def two : ConditionalExpr := .leaf (.const 2)
def denominator : ConditionalExpr := arithmeticTree .add cancelJump two

theorem correlated_denominator_unknown : coefficients .div one denominator = none := by decide +kernel

theorem cancelled_jump_value (t : ℝ) : ConditionalValue t 0 cancelJump 0 := by
  apply (arithmeticTree_value_iff t 0 .sub jumpTree jumpTree 0).mpr
  refine ⟨PiecewiseExamples.jump t,PiecewiseExamples.jump t,jump_semantic_value t,jump_semantic_value t,?_⟩
  change (0:ℝ) = PiecewiseExamples.jump t - PiecewiseExamples.jump t
  ring

theorem correlated_denominator_value (t : ℝ) : ConditionalValue t 0 denominator 2 := by
  apply (arithmeticTree_value_iff t 0 .add cancelJump two 2).mpr
  have h2 : ConditionalValue t 0 two 2 := by
    apply ConditionalValue.leaf
    simpa using (Value.const (x := t) (y := (0:ℝ)) 2)
  exact ⟨0,2,cancelled_jump_value t,h2,by norm_num [ArithmeticOp.Rel]⟩

theorem correlated_quotient_everywhere_defined (t : ℝ) :
    ConditionalArithmeticValue t 0 .div one denominator (1/2) :=
  ⟨1,2,one_value t 0,correlated_denominator_value t,by norm_num [ArithmeticOp.Rel]⟩

end GeneralizedIntervalArithmetic.ConditionalArithmeticExamples
