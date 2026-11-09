import ParameterRestriction
import Subdivision
import PiecewiseSelection

namespace GeneralizedIntervalArithmetic.ParameterRestrictionExamples

def unit : QInterval := ⟨0,1,by norm_num⟩
def left : ParameterCell := ⟨unit.lowerHalf,by decide +kernel,by decide +kernel⟩
def right : ParameterCell := ⟨unit.upperHalf,by decide +kernel,by decide +kernel⟩
def point : ParameterCell := ⟨.point (1/2),by norm_num [QInterval.point],by norm_num [QInterval.point]⟩

/-- Reuse the old split coverage theorem; no second subdivision algorithm. -/
theorem halves_cover : ParameterCover [left,right] := by
  intro t ht
  have hm : unit.Contains t := by simpa [unit,QInterval.Contains] using ht
  rcases (split_cover unit t).mp hm with hl | hr
  · exact ⟨left,by simp,hl⟩
  · exact ⟨right,by simp,hr⟩

theorem boundary_in_both : left.interval.Contains (1/2:ℝ) ∧ right.interval.Contains (1/2:ℝ) := by
  simpa [unit,QInterval.midpoint] using split_boundary unit

theorem left_endpoint_map : left.map 1 = (1/2:ℝ) := by
  norm_num [ParameterCell.map,left,unit,QInterval.lowerHalf,QInterval.midpoint]
theorem right_endpoint_map : right.map 0 = (1/2:ℝ) := by
  norm_num [ParameterCell.map,right,unit,QInterval.upperHalf,QInterval.midpoint]
theorem degenerate_map (s : ℝ) : point.map s = (1/2:ℝ) := by
  norm_num [ParameterCell.map,point,QInterval.point]
  ring

def X : LinearInterval := .exact ⟨0,1⟩
def Y : LinearInterval := .exact ⟨0,0⟩
def reciprocal : Expr := .div (.const 1) .x

def coefficients (C : ParameterCell) : Option (QAffine × QAffine) :=
  (evalGuarded (X.reparam C) (Y.reparam C) reciprocal).map (fun R => (R.lower,R.upper))

theorem whole_reciprocal_unknown : (evalGuarded X Y reciprocal).isNone = true := by decide +kernel

theorem right_reciprocal_bounds : coefficients right = some (⟨1,1⟩,⟨2,2⟩) := by decide +kernel

theorem left_touching_zero_unknown : coefficients left = none := by decide +kernel

theorem point_reciprocal_exact : coefficients point = some (⟨2,2⟩,⟨2,2⟩) := by decide +kernel

theorem strict_left_boundary_unknown : decideLinearLt (X.reparam left) (1/2) = .unknown := by
  decide +kernel

theorem strict_right_boundary_false : decideLinearLt (X.reparam right) (1/2) = .no := by
  decide +kernel

private theorem input_x (t : ℝ) : X.Contains t t := by
  apply (linear_exact_contains _ _ _).mpr
  simp [QAffine.value]
private theorem input_y (t : ℝ) : Y.Contains t 0 := by
  apply (linear_exact_contains _ _ _).mpr
  simp [QAffine.value]

theorem right_success : (evalGuarded (X.reparam right) (Y.reparam right) reciprocal).isSome := by
  decide +kernel

def rightResult : LinearInterval :=
  (evalGuarded (X.reparam right) (Y.reparam right) reciprocal).get right_success

theorem right_defined {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    ∃ z, Value (right.map s) 0 reciprocal z :=
  evalGuarded_defined hs ((linear_reparam_contains X right s _).mpr (input_x _))
    ((linear_reparam_contains Y right s _).mpr (input_y _))
    (Option.some_get right_success).symm

def punctured : DomainBounds ℝ :=
  ⟨fun t => t ≠ 1/2,fun t => t ≠ 1/2,fun _ h => h⟩
def everywhere : DomainBounds ℝ := ⟨fun _ => True,fun _ => True,fun _ h => h⟩
def RX (t x : ℝ) : Prop := t ∈ Set.Icc (0:ℝ) 1 ∧ t ≠ 1/2 ∧ x = t
def RY (t y : ℝ) : Prop := t ∈ Set.Icc (0:ℝ) 1 ∧ y = 0

theorem x_contract : (X.onDomain punctured).Sound RX := by
  refine ⟨?_,?_,?_⟩
  · rintro t x ⟨_,_,rfl⟩; exact input_x _
  · rintro t x ⟨ht,hn,_⟩; exact ⟨ht,hn⟩
  · rintro t ⟨ht,hn⟩; exact ⟨t,ht,hn,rfl⟩

theorem y_contract : (Y.onDomain everywhere).Sound RY := by
  refine ⟨?_,?_,?_⟩
  · rintro t y ⟨_,rfl⟩; exact input_y t
  · rintro t y ⟨ht,_⟩; exact ⟨ht,trivial⟩
  · rintro t ⟨ht,_⟩; exact ⟨0,ht,rfl⟩

theorem restricted_reciprocal_contract :
    (rightResult.onDomain ((right.pullDomain punctured).inter (right.pullDomain everywhere))).Sound
      (fun s z => s ∈ Set.Icc (0:ℝ) 1 ∧ ExpressionValues RX RY reciprocal (right.map s) z) :=
  evalGuarded_reparam_relational_sound right x_contract y_contract
    (Option.some_get right_success).symm

/-- Numerical success does not fill the excluded shared boundary. -/
theorem right_boundary_absent :
    ¬ ∃ z, (0:ℝ) ∈ Set.Icc 0 1 ∧ ExpressionValues RX RY reciprocal (right.map 0) z := by
  apply domain_absent restricted_reciprocal_contract
  intro h
  exact h.2.1 right_endpoint_map

theorem left_boundary_domain_absent : ¬ (left.pullDomain punctured).possible 1 := by
  exact fun h => h left_endpoint_map

theorem degenerate_domain_absent (s : ℝ) : ¬ (point.pullDomain punctured).possible s :=
  fun h => h (degenerate_map s)

theorem restricted_interior_defined :
    ∃ z, (1/2:ℝ) ∈ Set.Icc 0 1 ∧ ExpressionValues RX RY reciprocal (right.map (1/2)) z := by
  apply domain_definite restricted_reciprocal_contract
  change (1/2:ℝ) ∈ Set.Icc 0 1 ∧ right.map (1/2) ≠ 1/2 ∧ True
  norm_num [ParameterCell.map,right,unit,QInterval.upperHalf,QInterval.midpoint]

def positive : Expr := .add .x (.const 2)
def positiveResult (C : ParameterCell) : LinearInterval :=
  (X.reparam C).add (.exact ⟨2,2⟩)

theorem positive_success (C : ParameterCell) :
    evalGuarded (X.reparam C) (Y.reparam C) positive = some (positiveResult C) := rfl

theorem positive_on_cell (C : ParameterCell) {s z : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1)
    (hv : Value (C.map s) 0 positive z) : 0 < z := by
  have h := evalGuarded_sound hs
    ((linear_reparam_contains X C s _).mpr (input_x _))
    ((linear_reparam_contains Y C s _).mpr (input_y _)) hv (positive_success C)
  have hl := h.1
  change ((X.lower.reparam C).add ⟨2,2⟩).value s ≤ z at hl
  rw [affine_add_value,affine_reparam_value] at hl
  have hn := (parameter_map_unit C hs).1
  simp [X,LinearInterval.exact,QAffine.value] at hl
  linarith

/-- Recombine only via certified coverage, including the shared midpoint. -/
theorem covered_positive {t z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hv : Value t 0 positive z) : 0 < z :=
  parameter_cover_transfer halves_cover
    (R := fun t z => Value t 0 positive z) (P := fun _ z => 0 < z)
    (fun C _ _ hs _ hz => positive_on_cell C hs hz) ht hv

end GeneralizedIntervalArithmetic.ParameterRestrictionExamples
