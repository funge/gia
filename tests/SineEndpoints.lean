import SineEndpoints
import AuditPolicy

namespace GeneralizedIntervalArithmetic.SineEndpointChecks
open HardwareAddition HardwareSine

noncomputable def rlt (a b : ℝ) : Bool := by classical exact decide (a < b)
noncomputable def sub (I J : Bounds ℝ) : Option (Bounds ℝ) :=
  some ⟨I.lo - J.hi, I.hi - J.lo⟩

/-- An independent exact-real oracle checks composition, not native execution. -/
noncomputable def positive (I : Bounds ℝ) : Option (Bounds ℝ) := by
  classical
  exact if I.lo = I.hi then some ⟨Real.sin I.lo, Real.sin I.hi⟩ else none

theorem sub_sound : OpSound some sub (· - ·) := by
  intro I J O x y hr hx hy
  cases hr
  rcases hx with ⟨a, b, ha, hb, hl, hu⟩
  rcases hy with ⟨c, d, hc, hd, jl, ju⟩
  simp only [Option.some.injEq] at ha hb hc hd
  subst a; subst b; subst c; subst d
  exact ⟨_, _, rfl, rfl, sub_le_sub hl ju, sub_le_sub hu jl⟩

theorem positive_sound : RangeSound some positive := by
  intro I O x hr hx
  classical
  simp only [positive] at hr
  split at hr
  next he =>
    cases hr
    rcases hx with ⟨a, b, ha, hb, hl, hu⟩
    simp only [Option.some.injEq] at ha hb
    subst a; subst b
    have hx : x = I.lo := by rw [← he] at hu; exact le_antisymm hu hl
    subst x
    exact ⟨_, _, rfl, rfl, le_rfl, by rw [he]⟩
  · contradiction

theorem signed_composition {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) :
    Contains some (⟨-Real.sin 1, Real.sin 1⟩ : Bounds ℝ) (Real.sin x) := by
  apply signed_endpoints_enclose (lt := rlt) (zero := 0) (negOne := -1) (one := 1)
    (by simp [HardwareDivision.CompareSound, rlt]) rfl rfl rfl sub_sound positive_sound
    (I := ⟨-1, 1⟩)
  · norm_num [endpoints, signedPoint, unitGuard, rlt, sub, positive, Real.sin_neg]
  · exact ⟨-1, 1, rfl, rfl, hx.1, hx.2⟩

theorem endpoint_unit {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) :
    0 ≤ Real.sin x ∧ Real.sin x ≤ 101/120 := by
  have h := ideal_endpoint_bounds (a := 0) (b := 1) (by norm_num) (by norm_num) hx
  norm_num [SineTaylor.polynomial] at h ⊢
  exact h

/-- Extending endpoint-only evaluation to the full period would be unsound. -/
theorem no_global_monotonicity : ¬ Monotone Real.sin := by
  intro h
  have hh := h (show Real.pi/2 ≤ Real.pi by linarith [Real.pi_pos])
  norm_num at hh

theorem unsupported {F : Type} (point : F → Option (Bounds F)) (I : Bounds F) :
    endpoints (m := Id) (fun _ => false) point I = none := by simp [endpoints]

theorem failed_upper : endpoints (m := Id) (fun _ => true)
    (fun n : Nat => if n = 0 then some (⟨0, 0⟩ : Bounds Nat) else none) ⟨0, 1⟩ = none := by
  simp [endpoints]

theorem failed_reflection {F : Type} (zero a : F)
    (positive : Bounds F → Option (Bounds F)) :
    signedPoint (m := Id) (fun _ _ => true) zero (fun _ _ => none) positive a = none := by
  simp [signedPoint]

theorem external_hole :
    ¬ ∃ z, SinValues (fun (_ : Unit) (w x : ℝ) => w ≠ 0 ∧ x = w) () 0 z := by
  simp [sinValues_defined_iff]

end GeneralizedIntervalArithmetic.SineEndpointChecks
#audit_namespace GeneralizedIntervalArithmetic.SineEndpointChecks
