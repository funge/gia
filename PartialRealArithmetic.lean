import Mathlib.Data.Real.Basic

namespace GeneralizedIntervalArithmetic.PartialRealArithmetic

/-- Proof-side real operations. Division's value alone is totalized by Lean;
use `divRel` or pair `div` with `divDefined` for partial arithmetic semantics. -/
@[simp] noncomputable abbrev add (x y : ℝ) : ℝ := x + y
@[simp] noncomputable abbrev sub (x y : ℝ) : ℝ := x - y
@[simp] noncomputable abbrev mul (x y : ℝ) : ℝ := x * y
@[simp] noncomputable abbrev div (x y : ℝ) : ℝ := x / y

@[simp] abbrev totalDefined (_x _y : ℝ) : Prop := True
@[simp] abbrev divDefined (_x y : ℝ) : Prop := y ≠ 0

@[simp] abbrev addRel (x y z : ℝ) : Prop := z = add x y
@[simp] abbrev subRel (x y z : ℝ) : Prop := z = sub x y
@[simp] abbrev mulRel (x y z : ℝ) : Prop := z = mul x y
@[simp] abbrev divRel (x y z : ℝ) : Prop := divDefined x y ∧ z = div x y

theorem div_domain_iff (x y : ℝ) : (∃ z, divRel x y z) ↔ divDefined x y := by
  exact ⟨fun ⟨_,h,_⟩ => h, fun h => ⟨div x y,h,rfl⟩⟩

theorem div_zero (x z : ℝ) : ¬ divRel x 0 z := fun h => h.1 rfl

end GeneralizedIntervalArithmetic.PartialRealArithmetic
