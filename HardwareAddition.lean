import HardwareBounds
import Mathlib.Data.Real.Basic

namespace GeneralizedIntervalArithmetic.HardwareAddition

/-- `decode` is the adapter's finite-value interpretation; None has no real value. -/
def Contains {F : Type} (decode : F → Option ℝ) (I : Bounds F) (x : ℝ) : Prop :=
  ∃ l u, decode I.lo = some l ∧ decode I.hi = some u ∧ l ≤ x ∧ x ≤ u

/-- Contract for one observed directed-addition call. Failure is unconstrained.
This is a hypothesis, not an axiom or a proof of the hardware adapter. -/
def CallSound {F : Type} (decode : F → Option ℝ) (a b : F)
    (result : Option (F × F)) : Prop :=
  ∀ x y, decode a = some x → decode b = some y →
  ∀ p, result = some p → ∃ l u,
    decode p.1 = some l ∧ decode p.2 = some u ∧ l ≤ x + y ∧ x + y ≤ u

/-- Conditional hardware-result theorem. The two contracts are about the actual
observed calls on the lower/lower and upper/upper endpoints, respectively. -/
theorem assemble_encloses {F : Type} {decode : F → Option ℝ}
    {I J R : Bounds F} {lower upper : Option (F × F)}
    (hl : CallSound decode I.lo J.lo lower)
    (hu : CallSound decode I.hi J.hi upper)
    (hr : assemble lower upper = some R)
    {x y : ℝ} (hx : Contains decode I x) (hy : Contains decode J y) :
    Contains decode R (x + y) := by
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
      rcases hl il jl hil hjl l rfl with ⟨a, b, ha, _, hab, _⟩
      rcases hu ih jh hih hjh u rfl with ⟨c, d, _, hd, _, hcd⟩
      exact ⟨a, d, ha, hd, hab.trans (add_le_add hix hjy),
        (add_le_add hxi hyj).trans hcd⟩

theorem failure_is_unknown {F : Type} (upper : Option (F × F)) :
    assemble none upper = none := rfl

end GeneralizedIntervalArithmetic.HardwareAddition
