import HardwareDivision
import AuditPolicy
import Mathlib.Tactic.NormNum

namespace GeneralizedIntervalArithmetic.HardwareDivisionChecks
open HardwareAddition HardwareMultiplication HardwareDivision

noncomputable def realLt (a b : ℝ) : Bool := decide (a < b)

theorem real_comparison_sound : CompareSound (some : ℝ → Option ℝ) realLt := by
  simp [CompareSound, realLt]

theorem positive_denominator {x y : ℝ}
    (hx : Contains some ⟨-2, 3⟩ x) (hy : Contains some ⟨1, 2⟩ y) :
    Contains some ⟨-2, 3⟩ (x/y) ∧ y ≠ 0 := by
  apply assembleGuarded_encloses real_comparison_sound (zero := (0 : ℝ)) rfl
    (chooseMin := min) (chooseMax := max) (I := ⟨-2, 3⟩) (J := ⟨1, 2⟩)
    (ll := some ((-2 : ℝ), -2)) (lh := some ((-1 : ℝ), -1))
    (hl := some ((3 : ℝ), 3)) (hh := some ((3/2 : ℝ), 3/2))
    _ _ _ _ _ _ _ hx hy
  · simp [SelectSound]
  · simp [SelectSound]
  · norm_num [HardwareDivision.CallSound, ResultSound]
  · norm_num [HardwareDivision.CallSound, ResultSound]
  · norm_num [HardwareDivision.CallSound, ResultSound]
  · norm_num [HardwareDivision.CallSound, ResultSound]
  · norm_num [assembleGuarded, awayZero, realLt, assembleFour]

theorem negative_denominator {x y : ℝ}
    (hx : -2 ≤ x ∧ x ≤ 3) (hy : -2 ≤ y ∧ y ≤ -1) :
    -3 ≤ x/y ∧ x/y ≤ 2 := by
  have h := four_quotients hx hy (Or.inl (by norm_num))
  norm_num at h ⊢
  exact h

theorem crossing_zero_unknown (ll lh hl hh : Option (ℝ × ℝ)) :
    assembleGuarded realLt 0 min max ⟨-1, 1⟩ ll lh hl hh = none := by
  norm_num [assembleGuarded, awayZero, realLt]

theorem zero_boundary_unknown (ll lh hl hh : Option (ℝ × ℝ)) :
    assembleGuarded realLt 0 min max ⟨0, 1⟩ ll lh hl hh = none := by
  norm_num [assembleGuarded, awayZero, realLt]

theorem rejection_does_not_mean_nowhere_defined :
    awayZero realLt 0 ⟨-1, 1⟩ = false ∧ (1 : ℝ) / 1 = 1 := by
  norm_num [awayZero, realLt]

theorem incorrect_comparison_rejected :
    ¬ CompareSound (some : ℝ → Option ℝ) (fun _ _ => true) := by
  intro h
  have bad := h 0 0 0 0 rfl rfl
  norm_num at bad

#audit_namespace GeneralizedIntervalArithmetic.HardwareDivisionChecks
end GeneralizedIntervalArithmetic.HardwareDivisionChecks
