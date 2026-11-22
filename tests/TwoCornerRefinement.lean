import TwoCornerRefinement
import AuditPolicy
import Mathlib.Tactic.NormNum

namespace GeneralizedIntervalArithmetic.TwoCornerRefinementChecks
open HardwareAddition HardwareMultiplication TwoCornerRefinement

noncomputable def realLt (a b : ℝ) : Bool := decide (a < b)
theorem real_comparison : HardwareDivision.CompareSound some realLt := by
  simp [HardwareDivision.CompareSound,realLt]
theorem real_min : SelectSound (some : ℝ → Option ℝ) min min := by simp [SelectSound]
theorem real_max : SelectSound (some : ℝ → Option ℝ) max max := by simp [SelectSound]
theorem exact_call (a b : ℝ) : HardwareDivision.CallSound some a b (some (a/b,a/b)) := by
  simp [HardwareDivision.CallSound,ResultSound]

theorem guarded_positive : ∃ new : Bounds ℝ,
    assemble (some ((1:ℝ)/2,1/2)) (some (2,2)) = some new ∧
    Refines some new ⟨1/2,2⟩ ∧
    ∀ x y, Contains some ⟨1,2⟩ x → Contains some ⟨1,2⟩ y →
      Contains some new (x/y) ∧ y ≠ 0 := by
  apply guarded_refinement (I := ⟨(1:ℝ),2⟩) (J := ⟨1,2⟩)
    (ln := 1) (ld := 2) (un := 2) (ud := 1)
    (ll := some (1,1)) (lh := some (1/2,1/2)) (hl := some (2,2)) (hh := some (1,1))
    real_comparison (zero := 0) rfl real_min real_max
    rfl rfl rfl rfl (by norm_num) (by norm_num)
    (by norm_num [HardwareDivision.awayZero,realLt])
    (by norm_num [TwoCornerDivision.select,TwoCornerDivision.positiveCorners])
    rfl rfl rfl rfl
  · simpa using exact_call 1 1
  · simpa using exact_call 1 2
  · simpa using exact_call 2 1
  · simpa using exact_call 2 2
  · simp [observations]
  · simp [observations]
  · norm_num [HardwareDivision.assembleGuarded,HardwareDivision.awayZero,realLt,assembleFour]

theorem guarded_changed_unused_sides : ∃ new : Bounds ℝ,
    assemble (some ((1:ℝ)/2,99)) (some (-99,2)) = some new ∧
    Refines some new ⟨1/2,2⟩ ∧
    ∀ x y, Contains some ⟨1,2⟩ x → Contains some ⟨1,2⟩ y →
      Contains some new (x/y) ∧ y ≠ 0 := by
  obtain ⟨mid,hm,hr,hs⟩ := guarded_positive
  obtain ⟨new,hn,href,heq⟩ := direction_transfer hm hr
    (lower' := some ((1:ℝ)/2,99)) (upper' := some (-99,2)) rfl rfl
  refine ⟨new,hn,href,?_⟩
  intro x y hx hy
  have h := hs x y hx hy
  exact ⟨(heq (x/y)).mp h.1,h.2⟩

theorem subset_use {new old : Bounds ℝ} (h : Refines some new old)
    {z : ℝ} (hz : Contains some new z) : Contains some old z := h.contains hz

/-- Same paired observations, not newly generated outcomes. The omitted loose
pair widens the old result, so equality of widths is deliberately not claimed. -/
theorem loose_structural_refinement : ∃ new : Bounds ℝ,
    assemble (some ((1:ℝ)/2,1/2)) (some (2,2)) = some new ∧ Refines some new ⟨-10,10⟩ := by
  apply same_observations_refine real_min real_max
    (ll := some ((-10:ℝ),10)) (lh := some (1/2,1/2)) (hl := some (2,2)) (hh := some (1,1))
    (v₁ := 1) (v₂ := 1/2) (v₃ := 2) (v₄ := 1)
  all_goals norm_num [ResultSound,assembleFour]

theorem only_used_directions_need_agree : ∃ new : Bounds ℝ,
    assemble (some ((1:ℝ)/2,99)) (some (-99,2)) = some new ∧ Refines some new ⟨1/2,2⟩ := by
  apply directional_observations_refine real_min real_max
    (ll := some ((1:ℝ),1)) (lh := some (1/2,1/2)) (hl := some (2,2)) (hh := some (1,1))
    (lower := some (1/2,1/2)) (upper := some (2,2))
    (v₁ := 1) (v₂ := 1/2) (v₃ := 2) (v₄ := 1)
  all_goals norm_num [ResultSound,assembleFour,downValue,upValue]

theorem omitted_failure_asymmetry :
    assemble (some ((1:ℝ)/2,1/2)) (some (2,2)) = some ⟨1/2,2⟩ ∧
    assembleFour min max (none : Option (ℝ × ℝ)) (some (1/2,1/2))
      (some (2,2)) (some (1,1)) = none := by
  norm_num [assemble,assembleFour]

theorem omitted_failure_contract : HardwareDivision.CallSound some (1:ℝ) 1 none := by
  simp [HardwareDivision.CallSound,ResultSound]

theorem selected_failure : assemble (none : Option (ℝ × ℝ)) (some (2,2)) = none := rfl

/-- The pair directions matter for enclosure: an observed upper endpoint may
not be substituted for the selected Down result. -/
theorem wrong_direction : ResultSound some (some ((0:ℝ),2)) 1 ∧
    assemble (some ((0:ℝ),2)) (some (0,2)) = some ⟨0,2⟩ ∧
    ¬ Contains some ⟨(2:ℝ),2⟩ 1 := by
  norm_num [ResultSound,assemble,Contains]

-- Abstract invalid/nonfinite token, not native infinity bits or an FFI test.
def invalidUpper : Bounds (Option ℝ) := ⟨some 1,none⟩
theorem naive_unused_nonfinite :
    assemble (some (some (-1:ℝ),some (-1:ℝ))) (some (some (1:ℝ),some (1:ℝ))) =
      some ⟨some (-1:ℝ),some (1:ℝ)⟩ ∧
    ¬ ∃ d : ℝ, (id invalidUpper.hi : Option ℝ) = some d := by
  simp [assemble,invalidUpper]

theorem selected_calls_with_invalid_unused_endpoint :
    HardwareDivision.CallSound (id : Option ℝ → Option ℝ) (some (-1)) (some 1)
      (some (some (-1),some (-1))) ∧
    HardwareDivision.CallSound (id : Option ℝ → Option ℝ) (some 1) (some 1)
      (some (some 1,some 1)) := by
  norm_num [HardwareDivision.CallSound,ResultSound]

-- Two distinct abstract zero tags, with the same real interpretation. This
-- controls decoded containment versus raw equality, without modeling binary64.
def zeroDecode (_ : Bool) : Option ℝ := some 0
def leftTag (a _ : Bool) : Bool := a
def rightTag (_ b : Bool) : Bool := b

theorem left_min_sound : SelectSound zeroDecode leftTag min := by simp [SelectSound,zeroDecode]
theorem left_max_sound : SelectSound zeroDecode leftTag max := by simp [SelectSound,zeroDecode]
theorem right_min_sound : SelectSound zeroDecode rightTag min := by simp [SelectSound,zeroDecode]

theorem zero_tie_representation_difference :
    assembleFour leftTag leftTag (some (false,false)) (some (true,true))
      (some (true,true)) (some (false,false)) = some ⟨false,false⟩ ∧
    assemble (some (true,true)) (some (true,true)) = some ⟨true,true⟩ ∧
    (⟨true,true⟩ : Bounds Bool) ≠ ⟨false,false⟩ ∧
    Refines zeroDecode ⟨true,true⟩ ⟨false,false⟩ := by
  refine ⟨rfl,rfl,?_,?_⟩
  · intro h
    have he := congrArg Bounds.lo h
    cases he
  · exact ⟨0,0,0,0,rfl,rfl,rfl,rfl,le_rfl,le_rfl⟩

theorem tie_choices_both_sound : leftTag false true ≠ rightTag false true ∧
    zeroDecode (leftTag false true) = zeroDecode (rightTag false true) := by
  simp [leftTag,rightTag,zeroDecode]

theorem zero_directions_agree :
    downValue zeroDecode (some (true,false)) = downValue zeroDecode (some (false,false)) ∧
    upValue zeroDecode (some (false,true)) = upValue zeroDecode (some (false,false)) := by
  constructor <;> rfl

#audit_namespace GeneralizedIntervalArithmetic.TwoCornerRefinementChecks
end GeneralizedIntervalArithmetic.TwoCornerRefinementChecks
