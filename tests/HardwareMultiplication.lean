import HardwareMultiplication
import AuditPolicy
import Mathlib.Tactic.NormNum

namespace GeneralizedIntervalArithmetic.HardwareMultiplicationChecks

theorem mixed_sign_corners {x y : ℝ}
    (hx : -2 ≤ x ∧ x ≤ 3) (hy : -4 ≤ y ∧ y ≤ 5) :
    -12 ≤ x*y ∧ x*y ≤ 15 := by
  have h := HardwareMultiplication.rounded_corners_enclose hx hy
    (l₁ := 8) (u₁ := 8) (l₂ := -10) (u₂ := -10)
    (l₃ := -12) (u₃ := -12) (l₄ := 15) (u₄ := 15)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem thesis_positive_right {x y : ℝ}
    (hx : -2 ≤ x ∧ x ≤ 3) (hy : 5 ≤ y ∧ y ≤ 7) :
    -14 ≤ x*y ∧ x*y ≤ 21 := by
  have h := four_products hx hy
  norm_num at h ⊢
  exact h

theorem wrong_selection_misses : ¬ ((-10 : ℝ) ≤ 3 * (-4)) := by norm_num

theorem diagonal_corners_insufficient :
    min ((-2 : ℝ)*(-4)) (3*5) > 3*(-4) := by norm_num

open HardwareAddition HardwareMultiplication

theorem assembled_thesis_enclosure {x y : ℝ}
    (hx : Contains some ⟨-2, 3⟩ x) (hy : Contains some ⟨5, 7⟩ y) :
    Contains some ⟨-14, 21⟩ (x*y) := by
  apply assembleFour_encloses
    (chooseMin := min) (chooseMax := max) (I := ⟨-2, 3⟩) (J := ⟨5, 7⟩)
    (ll := some ((-10 : ℝ), -10)) (lh := some ((-14 : ℝ), -14))
    (hl := some ((15 : ℝ), 15)) (hh := some ((21 : ℝ), 21))
    _ _ _ _ _ _ _ hx hy
  · simp [SelectSound]
  · simp [SelectSound]
  · norm_num [HardwareMultiplication.CallSound]
  · norm_num [HardwareMultiplication.CallSound]
  · norm_num [HardwareMultiplication.CallSound]
  · norm_num [HardwareMultiplication.CallSound]
  · norm_num [assembleFour]

theorem wrong_min_selector_rejected :
    ¬ SelectSound (some : ℝ → Option ℝ) max min := by
  intro h
  have bad := h 0 1 0 1 rfl rfl
  norm_num at bad

theorem every_missing_corner_unknown :
    let p := some ((1 : ℝ), 2)
    assembleFour min max none p p p = none ∧
    assembleFour min max p none p p = none ∧
    assembleFour min max p p none p = none ∧
    assembleFour min max p p p none = none := by
  simp [assembleFour]

#audit_namespace GeneralizedIntervalArithmetic.HardwareMultiplicationChecks
end GeneralizedIntervalArithmetic.HardwareMultiplicationChecks
