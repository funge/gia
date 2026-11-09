import HardwareAddition

namespace GeneralizedIntervalArithmetic.HardwareSubtraction
open HardwareAddition

/-- Same finite directed-operation boundary as addition, instantiated for subtraction.
The contract concerns an observed call; it is not an axiom about native execution. -/
def CallSound {F : Type} (decode : F → Option ℝ) (a b : F)
    (result : Option (F × F)) : Prop :=
  ∀ x y, decode a = some x → decode b = some y →
  ∀ p, result = some p → ∃ l u,
    decode p.1 = some l ∧ decode p.2 = some u ∧ l ≤ x - y ∧ x - y ≤ u

/-- Subtraction reverses the second endpoint order. The executable uses these
same lower/upper calls and the existing pure assembly function. -/
theorem assemble_encloses {F : Type} {decode : F → Option ℝ}
    {I J R : Bounds F} {lower upper : Option (F × F)}
    (hl : CallSound decode I.lo J.hi lower)
    (hu : CallSound decode I.hi J.lo upper)
    (hr : assemble lower upper = some R)
    {x y : ℝ} (hx : Contains decode I x) (hy : Contains decode J y) :
    Contains decode R (x - y) := by
  rcases hx with ⟨il, ih, hil, hih, hix, hxi⟩
  rcases hy with ⟨jl, jh, hjl, hjh, hjy, hyj⟩
  cases lower with
  | none => simp [assemble] at hr
  | some l =>
    cases upper with
    | none => simp [assemble] at hr
    | some u =>
      simp [assemble] at hr
      subst R
      rcases hl il jh hil hjh l rfl with ⟨a, b, ha, _, hab, _⟩
      rcases hu ih jl hih hjl u rfl with ⟨c, d, _, hd, _, hcd⟩
      exact ⟨a, d, ha, hd, hab.trans (sub_le_sub hix hyj),
        (sub_le_sub hxi hjy).trans hcd⟩

end GeneralizedIntervalArithmetic.HardwareSubtraction
