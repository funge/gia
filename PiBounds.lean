import HardwareAddition
import Mathlib.Data.Real.Pi.Bounds

namespace GeneralizedIntervalArithmetic.HardwarePi
open HardwareAddition

/-- Exact dyadic values represented by binary64 bits 0x400921fb54442d18/19. -/
noncomputable def lower : ℝ := 7074237752028440 / 2251799813685248
noncomputable def upper : ℝ := 7074237752028441 / 2251799813685248

theorem bounds : lower < Real.pi ∧ Real.pi < upper := by
  constructor
  · have h := Real.pi_gt_d20
    norm_num [lower] at ⊢
    linarith
  · have h := Real.pi_lt_d20
    norm_num [upper] at ⊢
    linarith

theorem width : upper - lower = 1 / (2:ℝ)^51 := by norm_num [upper, lower]

/-- Instantiating existing finite constant decoding obligations suffices. The
mathematical containment of pi is proved, not another adapter assumption. -/
theorem decoded_contains {F : Type} {decode : F → Option ℝ} {lo hi : F}
    (hl : decode lo = some lower) (hu : decode hi = some upper) :
    Contains decode (⟨lo, hi⟩ : Bounds F) Real.pi :=
  ⟨lower, upper, hl, hu, bounds.1.le, bounds.2.le⟩

/-- Replacing pi by the lower endpoint as an exact constant loses containment. -/
theorem lower_singleton_misses : ¬ Contains some (⟨lower, lower⟩ : Bounds ℝ) Real.pi := by
  rintro ⟨a, b, ha, hb, _, hu⟩
  simp only [Option.some.injEq] at ha hb
  subst a; subst b
  exact (not_le_of_gt bounds.1) hu

end GeneralizedIntervalArithmetic.HardwarePi
