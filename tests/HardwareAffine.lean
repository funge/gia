import HardwareAffine
import HardwareSine
import AuditPolicy

namespace GeneralizedIntervalArithmetic.HardwareAffineChecks
open HardwareAffine

def exactLine : Form ℝ := ⟨⟨0,0⟩,⟨1,1⟩⟩

theorem shared_parameter (t : ℝ) : Contains some exactLine t t := by
  refine ⟨0,1,?_,?_,?_⟩
  · norm_num [exactLine, HardwareAddition.Contains]
  · norm_num [exactLine, HardwareAddition.Contains]
  · ring

theorem independent_parameters_do_not_cancel : (0:ℝ) - 1 ≠ 0 := by norm_num

theorem hull_needs_unit_parameter :
    Contains some exactLine 2 2 ∧
    ¬ HardwareAddition.Contains some (hull min max exactLine) 2 := by
  exact ⟨shared_parameter 2, by norm_num [hull,exactLine,HardwareAddition.Contains]⟩

theorem uncertain_self_difference_is_not_zero :
    Contains some (⟨⟨-1,1⟩,⟨-1,1⟩⟩ : Form ℝ) (1/2) 1 := by
  refine ⟨1,1,?_,?_,?_⟩ <;> norm_num [HardwareAddition.Contains]

-- A genuine non-singleton original linear interval is covered by the bridge.
theorem nonexact_bridge (I : LinearInterval) {t z : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hz : I.Contains t z) :
    Contains some
      ⟨⟨I.lower.atZero,I.upper.atZero⟩,⟨I.lower.atOne,I.upper.atOne⟩⟩ t z := by
  apply linear_bridge I _ _ _ _ ht hz
  all_goals
    simp only [HardwareAddition.Contains, Option.some.injEq]
    try { exact ⟨_,_,rfl,rfl,le_rfl,by exact_mod_cast I.orderedZero⟩ }
    try { exact ⟨_,_,rfl,rfl,by exact_mod_cast I.orderedZero,le_rfl⟩ }
    try { exact ⟨_,_,rfl,rfl,le_rfl,by exact_mod_cast I.orderedOne⟩ }
    try { exact ⟨_,_,rfl,rfl,by exact_mod_cast I.orderedOne,le_rfl⟩ }

noncomputable def secondFails (a _ : HardwareAddition.Bounds ℝ) : Option (HardwareAddition.Bounds ℝ) :=
  if a.lo = 0 then some a else none

theorem second_failure_discards_first :
    combine (m := Id) secondFails exactLine exactLine = none := by
  norm_num [combine,secondFails,exactLine]

-- Discharge the general interval-operation hypotheses using existing directed
-- call contracts. This is a composition check, not a new native axiom.
theorem directed_subtraction {F : Type} {decode : F → Option ℝ}
    {call : F → F → Option (F × F)}
    (hc : ∀ a b, HardwareSubtraction.CallSound decode a b (call a b))
    {I J O : Form F} {t x y : ℝ}
    (hr : combine (m := Id)
      (fun A B => HardwareAddition.assemble (call A.lo B.hi) (call A.hi B.lo)) I J = some O)
    (hx : Contains decode I t x) (hy : Contains decode J t y) :
    Contains decode O t (x-y) :=
  sub_sound (HardwareSine.sub_op_sound hc) hr hx hy

theorem directed_scalar {F : Type} {decode : F → Option ℝ}
    {call : F → F → Option (F × F)} {mn mx : F → F → F}
    (hc : ∀ a b, HardwareMultiplication.CallSound decode a b (call a b))
    (hmin : HardwareMultiplication.SelectSound decode mn min)
    (hmax : HardwareMultiplication.SelectSound decode mx max)
    {I O : Form F} {C : HardwareAddition.Bounds F} {t x c : ℝ}
    (hr : scale (m := Id) (fun A B => HardwareMultiplication.assembleFour mn mx
      (call A.lo B.lo) (call A.lo B.hi) (call A.hi B.lo) (call A.hi B.hi)) C I = some O)
    (hs : HardwareAddition.Contains decode C c) (hx : Contains decode I t x) :
    Contains decode O t (c*x) :=
  scale_sound (HardwareSine.mul_op_sound hmin hmax hc) hr hs hx

#audit_namespace GeneralizedIntervalArithmetic.HardwareAffineChecks
end GeneralizedIntervalArithmetic.HardwareAffineChecks
