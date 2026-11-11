import PiBounds

namespace GeneralizedIntervalArithmetic.HardwarePi
open HardwareAddition

noncomputable def tailLower : ℝ := 2483825185828341 / 20282409603651670423947251286016
noncomputable def tailUpper : ℝ := 1242014004962189 / 10141204801825835211973625643008

theorem tail_bounds : tailLower < Real.pi - lower ∧ Real.pi - lower < tailUpper := by
  have hl := Real.pi_gt_d20
  have hu := Real.pi_lt_d20
  norm_num [tailLower,tailUpper,lower] at ⊢
  constructor <;> linarith

theorem tail_width : 0 < tailUpper-tailLower ∧ tailUpper-tailLower < 1001/(10:ℝ)^23 := by
  norm_num [tailLower,tailUpper]

theorem tail_contains {F : Type} {decode : F → Option ℝ} {lo hi : F}
    (hl : decode lo = some tailLower) (hu : decode hi = some tailUpper) :
    Contains decode (⟨lo,hi⟩ : Bounds F) (Real.pi-lower) :=
  ⟨tailLower,tailUpper,hl,hu,tail_bounds.1.le,tail_bounds.2.le⟩

end GeneralizedIntervalArithmetic.HardwarePi
