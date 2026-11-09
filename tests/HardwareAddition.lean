import HardwareAddition
import AuditPolicy
import Mathlib.Tactic.NormNum

namespace GeneralizedIntervalArithmetic.HardwareAdditionChecks
open HardwareAddition

-- Semantic controls use real values solely as a proof test, never as the hardware runtime.
theorem rounded_inward_rejected :
    ¬ CallSound (some : ℝ → Option ℝ) 1 0 (some (2, 2)) := by
  intro h
  obtain ⟨l, u, hl, _, hb, _⟩ := h 1 0 rfl rfl (2, 2) rfl
  simp only [Option.some.injEq] at hl
  subst l
  norm_num at hb

theorem missing_upper_unknown : assemble (some ((1 : ℝ), 2)) none = none := rfl

theorem both_calls_failed_unknown :
    assemble (F := Float) none none = none := rfl

-- Success does not mean that a malformed input contains any real point.
theorem reversed_input_has_no_member (x : ℝ) :
    ¬ Contains (some : ℝ → Option ℝ) ⟨2, 1⟩ x := by
  rintro ⟨l, u, hl, hu, hx, hxu⟩
  simp only [Option.some.injEq] at hl hu
  subst l; subst u
  have := hx.trans hxu
  norm_num at this

#audit_namespace GeneralizedIntervalArithmetic.HardwareAdditionChecks
end GeneralizedIntervalArithmetic.HardwareAdditionChecks
