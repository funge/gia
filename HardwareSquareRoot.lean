import HardwareMultiplication
import SquareRootDomains

namespace GeneralizedIntervalArithmetic.HardwareSquareRoot
open HardwareAddition HardwareMultiplication

/-- Contract for one observed directed square-root call at a nonnegative input.
Failure is unconstrained; this is a hypothesis, not a native implementation proof. -/
def CallSound {F : Type} (decode : F → Option ℝ) (a : F)
    (result : Option (F × F)) : Prop :=
  ∀ x, decode a = some x → 0 ≤ x → ResultSound decode result (Real.sqrt x)

/-- Clipping to zero encloses every defined root, including mixed-domain inputs.
The primitive contracts are about the clipped lower endpoint and original upper. -/
theorem assemble_encloses {F : Type} {decode : F → Option ℝ}
    {chooseMax : F → F → F} {zero : F}
    (hz : decode zero = some 0) (hmax : SelectSound decode chooseMax max)
    {I R : Bounds F} {lower upper : Option (F × F)}
    (hl : CallSound decode (chooseMax I.lo zero) lower)
    (hu : CallSound decode I.hi upper)
    (hr : assemble lower upper = some R)
    {x : ℝ} (hx : Contains decode I x) (h0 : 0 ≤ x) :
    Contains decode R (Real.sqrt x) := by
  rcases hx with ⟨a, b, ha, hb, hax, hxb⟩
  have hc := hmax _ _ _ _ ha hz
  cases lower with
  | none => simp [assemble] at hr
  | some l =>
    cases upper with
    | none => simp [assemble] at hr
    | some u =>
      simp [assemble] at hr
      subst R
      rcases hl _ hc (le_max_right a 0) l rfl with ⟨c, d, hcl, _, hcs, _⟩
      rcases hu _ hb (h0.trans hxb) u rfl with ⟨e, f, _, hfu, _, hsf⟩
      exact ⟨c, f, hcl, hfu,
        hcs.trans (Real.sqrt_le_sqrt (max_le hax h0)),
        (Real.sqrt_le_sqrt hxb).trans hsf⟩

/-- Bridge to the existing partial root relation: no value is invented for x < 0,
and incoming witness/domain restrictions are retained in SqrtValues. -/
theorem assemble_sqrtValues {F α W : Type} {decode : F → Option ℝ}
    {chooseMax : F → F → F} {zero : F}
    (hz : decode zero = some 0) (hmax : SelectSound decode chooseMax max)
    {I O : Bounds F} {lower upper : Option (F × F)}
    (hl : CallSound decode (chooseMax I.lo zero) lower)
    (hu : CallSound decode I.hi upper) (ho : assemble lower upper = some O)
    {R : α → W → ℝ → Prop} {p : α} {w : W} {z : ℝ}
    (hi : ∀ x, R p w x → Contains decode I x) (hs : SqrtValues R p w z) :
    Contains decode O z := by
  rcases hs with ⟨x, hx, h0, rfl⟩
  exact assemble_encloses hz hmax hl hu ho (hi x hx) h0

/-- Nonnegative input bounds preserve the existing domain, for this witness. -/
theorem nonnegative_defined_iff {F α W : Type} {decode : F → Option ℝ}
    {I : Bounds F} {a : ℝ} (ha : decode I.lo = some a) (h0 : 0 ≤ a)
    {R : α → W → ℝ → Prop} {p : α} {w : W}
    (hi : ∀ x, R p w x → Contains decode I x) :
    (∃ z, SqrtValues R p w z) ↔ ∃ x, R p w x := by
  rw [sqrt_values_defined_iff]
  constructor
  · rintro ⟨x, hx, _⟩; exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨l, u, hl, _, hlx, _⟩ := hi x hx
    have he : l = a := Option.some.inj (hl.symm.trans ha)
    exact ⟨x, hx, h0.trans (he ▸ hlx)⟩

/-- A negative upper bound excludes all defined roots, independently of runtime
failure. Failure alone carries no such domain certificate. -/
theorem negative_absent {F α W : Type} {decode : F → Option ℝ}
    {I : Bounds F} {b : ℝ} (hb : decode I.hi = some b) (hn : b < 0)
    {R : α → W → ℝ → Prop} {p : α} {w : W}
    (hi : ∀ x, R p w x → Contains decode I x) : ¬ ∃ z, SqrtValues R p w z := by
  rintro ⟨z, x, hx, h0, _⟩
  obtain ⟨l, u, _, hu, _, hxu⟩ := hi x hx
  have he : u = b := Option.some.inj (hu.symm.trans hb)
  exact (not_le_of_gt hn) (h0.trans (he ▸ hxu))

end GeneralizedIntervalArithmetic.HardwareSquareRoot
