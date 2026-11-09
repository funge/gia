import HardwareSubtraction
import AuditPolicy
import Mathlib.Tactic.NormNum

namespace GeneralizedIntervalArithmetic.HardwareSubtractionChecks
open HardwareAddition

-- These real-valued controls test the theorem, not the executable backend.
theorem crossed_corners_enclose {x y : ℝ}
    (hx : Contains some ⟨1, 2⟩ x) (hy : Contains some ⟨3, 4⟩ y) :
    Contains some ⟨-3, -1⟩ (x - y) := by
  apply HardwareSubtraction.assemble_encloses
    (lower := some ((-3 : ℝ), -3)) (upper := some ((-1 : ℝ), -1))
    (I := ⟨1, 2⟩) (J := ⟨3, 4⟩) _ _ rfl hx hy
  · norm_num [HardwareSubtraction.CallSound]
  · norm_num [HardwareSubtraction.CallSound]

theorem same_corners_miss_endpoint :
    Contains (some : ℝ → Option ℝ) ⟨1, 2⟩ 1 ∧
    Contains (some : ℝ → Option ℝ) ⟨3, 4⟩ 4 ∧
    ¬ Contains (some : ℝ → Option ℝ) ⟨-2, -2⟩ (1 - 4) := by
  norm_num [Contains]

theorem inward_result_rejected :
    ¬ HardwareSubtraction.CallSound (some : ℝ → Option ℝ) 1 4 (some (-2, -2)) := by
  norm_num [HardwareSubtraction.CallSound]

theorem failure_contract_is_inconclusive :
    HardwareSubtraction.CallSound (some : ℝ → Option ℝ) 1 4 none ∧
    assemble (F := ℝ) none (some (-1, -1)) = none := by
  simp [HardwareSubtraction.CallSound, assemble]

#audit_namespace GeneralizedIntervalArithmetic.HardwareSubtractionChecks
end GeneralizedIntervalArithmetic.HardwareSubtractionChecks
