import HardwareSquareRoot
import AuditPolicy
import Mathlib.Tactic.NormNum

namespace GeneralizedIntervalArithmetic.HardwareSquareRootChecks
open HardwareAddition HardwareMultiplication HardwareSquareRoot

theorem sqrt_four : Real.sqrt 4 = 2 := by norm_num [Real.sqrt_eq_cases]

theorem mixed_enclosure {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 4) (h0 : 0 ≤ x) :
    Contains some ⟨0, 2⟩ (Real.sqrt x) := by
  apply assemble_encloses (zero := (0 : ℝ)) rfl (chooseMax := max)
    (I := ⟨-1, 4⟩) (lower := some ((0 : ℝ), 0)) (upper := some ((2 : ℝ), 2))
    _ _ _ rfl ⟨-1, 4, rfl, rfl, hx⟩ h0
  · simp [SelectSound]
  · norm_num [HardwareSquareRoot.CallSound, ResultSound]
  · norm_num [HardwareSquareRoot.CallSound, ResultSound, sqrt_four]

theorem nonnegative_enclosure {x : ℝ} (hx : 1 ≤ x ∧ x ≤ 4) :
    Contains some ⟨1, 2⟩ (Real.sqrt x) := by
  apply assemble_encloses (zero := (0 : ℝ)) rfl (chooseMax := max)
    (I := ⟨1, 4⟩) (lower := some ((1 : ℝ), 1)) (upper := some ((2 : ℝ), 2))
    _ _ _ rfl ⟨1, 4, rfl, rfl, hx⟩ (by linarith)
  · simp [SelectSound]
  · norm_num [HardwareSquareRoot.CallSound, ResultSound]
  · norm_num [HardwareSquareRoot.CallSound, ResultSound, sqrt_four]

/-- A caller's external hole is not filled by the numeric clipping operation. -/
def Restricted (allowed : Bool) (_ : Unit) (x z : ℝ) : Prop := allowed = true ∧ z = x

theorem mixed_defined_iff (allowed : Bool) (x : ℝ) :
    (∃ z, SqrtValues (Restricted allowed) () x z) ↔ allowed = true ∧ 0 ≤ x := by
  simp [sqrt_values_defined_iff, Restricted]

theorem bridge_keeps_witness {x z : ℝ} (hx : -1 ≤ x ∧ x ≤ 4)
    (hs : SqrtValues (Restricted true) () x z) : Contains some ⟨0, 2⟩ z := by
  apply assemble_sqrtValues (zero := (0 : ℝ)) rfl (chooseMax := max)
    (I := ⟨-1, 4⟩) (lower := some ((0 : ℝ), 0)) (upper := some ((2 : ℝ), 2))
    _ _ _ rfl _ hs
  · simp [SelectSound]
  · norm_num [HardwareSquareRoot.CallSound, ResultSound]
  · norm_num [HardwareSquareRoot.CallSound, ResultSound, sqrt_four]
  · intro v hv
    obtain ⟨_, rfl⟩ := hv
    exact ⟨-1, 4, rfl, rfl, hx⟩

theorem external_hole (x : ℝ) : ¬ ∃ z, SqrtValues (Restricted false) () x z := by
  simp [mixed_defined_iff]

theorem mixed_does_not_define_negative :
    ¬ ∃ z, SqrtValues (Restricted true) () (-1) z := by
  norm_num [mixed_defined_iff]

theorem mixed_has_defined_values : ∃ z, SqrtValues (Restricted true) () 4 z := by
  norm_num [mixed_defined_iff]

theorem totalized_root_is_not_partial :
    Real.sqrt (-1) = 0 ∧ ¬ SqrtValues (Restricted true) () (-1) 0 := by
  norm_num [SqrtValues, Restricted, Real.sqrt_eq_zero_of_nonpos]

theorem nonnegative_preserves_domain (allowed : Bool) {x : ℝ} (hx : 1 ≤ x ∧ x ≤ 4) :
    (∃ z, SqrtValues (Restricted allowed) () x z) ↔ ∃ v, Restricted allowed () x v := by
  apply nonnegative_defined_iff (I := (⟨1, 4⟩ : Bounds ℝ))
    (decode := some) rfl (by norm_num)
  intro v hv
  obtain ⟨_, rfl⟩ := hv
  exact ⟨1, 4, rfl, rfl, hx⟩

theorem negative_range_absent (allowed : Bool) {x : ℝ} (hx : -4 ≤ x ∧ x ≤ -1) :
    ¬ ∃ z, SqrtValues (Restricted allowed) () x z := by
  apply negative_absent (I := (⟨-4, -1⟩ : Bounds ℝ))
    (decode := some) rfl (by norm_num)
  intro v hv
  obtain ⟨_, rfl⟩ := hv
  exact ⟨-4, -1, rfl, rfl, hx⟩

theorem bad_primitive_contract_rejected :
    ¬ HardwareSquareRoot.CallSound (some : ℝ → Option ℝ) 1 (some (0, 0)) := by
  norm_num [HardwareSquareRoot.CallSound, ResultSound]

theorem unavailable_is_unknown (upper : Option (ℝ × ℝ)) : assemble none upper = none := rfl

#audit_namespace GeneralizedIntervalArithmetic.HardwareSquareRootChecks
end GeneralizedIntervalArithmetic.HardwareSquareRootChecks
