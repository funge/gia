import HardwareSine
import AuditPolicy

namespace GeneralizedIntervalArithmetic.HardwareSineChecks
open HardwareAddition HardwareSine

noncomputable def exactCall (f : ℝ → ℝ → ℝ) (a b : ℝ) : Option (ℝ × ℝ) :=
  some (f a b, f a b)

noncomputable def radd (I J : Bounds ℝ) :=
  assemble (exactCall (· + ·) I.lo J.lo) (exactCall (· + ·) I.hi J.hi)
noncomputable def rsub (I J : Bounds ℝ) :=
  assemble (exactCall (· - ·) I.lo J.hi) (exactCall (· - ·) I.hi J.lo)
noncomputable def rmul (I J : Bounds ℝ) :=
  HardwareMultiplication.assembleFour min max
    (exactCall (· * ·) I.lo J.lo) (exactCall (· * ·) I.lo J.hi)
    (exactCall (· * ·) I.hi J.lo) (exactCall (· * ·) I.hi J.hi)
noncomputable def rlt (a b : ℝ) : Bool := by classical exact decide (a < b)
noncomputable def rdiv (I J : Bounds ℝ) :=
  HardwareDivision.assembleGuarded rlt 0 min max J
    (exactCall (· / ·) I.lo J.lo) (exactCall (· / ·) I.lo J.hi)
    (exactCall (· / ·) I.hi J.lo) (exactCall (· / ·) I.hi J.hi)

theorem radd_sound : OpSound some radd (· + ·) := by
  apply add_op_sound
  simp [HardwareAddition.CallSound, exactCall]
theorem rsub_sound : OpSound some rsub (· - ·) := by
  apply sub_op_sound
  simp [HardwareSubtraction.CallSound, exactCall]
theorem rmul_sound : OpSound some rmul (· * ·) := by
  apply mul_op_sound
  · simp [HardwareMultiplication.SelectSound]
  · simp [HardwareMultiplication.SelectSound]
  · simp [HardwareMultiplication.CallSound, exactCall]
theorem rdiv_sound : OpSound some rdiv (· / ·) := by
  apply div_op_sound rfl
  · simp [HardwareDivision.CompareSound, rlt]
  · simp [HardwareMultiplication.SelectSound]
  · simp [HardwareMultiplication.SelectSound]
  · simp [HardwareDivision.CallSound, HardwareMultiplication.ResultSound, exactCall]

theorem radd_eq (I J : Bounds ℝ) :
    radd I J = some ⟨I.lo + J.lo, I.hi + J.hi⟩ := rfl

theorem rsub_eq (I J : Bounds ℝ) :
    rsub I J = some ⟨I.lo - J.hi, I.hi - J.lo⟩ := rfl

theorem rmul_point (a b : ℝ) : rmul ⟨a, a⟩ ⟨b, b⟩ = some ⟨a*b, a*b⟩ := by
  simp [rmul, exactCall, HardwareMultiplication.assembleFour]

theorem rdiv_point (a b : ℝ) (hb : 0 < b) :
    rdiv ⟨a, a⟩ ⟨b, b⟩ = some ⟨a/b, a/b⟩ := by
  simp [rdiv, rlt, exactCall, HardwareDivision.assembleGuarded,
    HardwareDivision.awayZero, HardwareMultiplication.assembleFour, hb]

theorem rmul_unit : rmul ⟨0, 1⟩ ⟨0, 1⟩ = some ⟨0, 1⟩ := by
  norm_num [rmul, exactCall, HardwareMultiplication.assembleFour]

theorem rdiv_unit (b : ℝ) (hb : 0 < b) :
    rdiv ⟨0, 1⟩ ⟨b, b⟩ = some ⟨0, 1/b⟩ := by
  have h : (0 : ℝ) ≤ 1/b := by positivity
  simp [rdiv, rlt, exactCall, HardwareDivision.assembleGuarded,
    HardwareDivision.awayZero, HardwareMultiplication.assembleFour, hb,
    min_eq_left h, max_eq_right h, hb.le]

/-- An independent real-arithmetic client of the same program, composed through
all four primitive-to-interval theorems. This is a proof fixture, not the runtime. -/
theorem composed_at_one : Contains some (⟨4241/5040, 101/120⟩ : Bounds ℝ) (Real.sin 1) := by
  refine run_encloses radd_sound rsub_sound rmul_sound rdiv_sound
    (supported := fun _ => true) (zero := 0) rfl
    (six := ⟨6, 6⟩) (oneTwenty := ⟨120, 120⟩) (fiveThousandForty := ⟨5040, 5040⟩)
    (I := ⟨1, 1⟩) ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨6, 6, rfl, rfl, le_rfl, le_rfl⟩
  · exact ⟨120, 120, rfl, rfl, le_rfl, le_rfl⟩
  · exact ⟨5040, 5040, rfl, rfl, le_rfl, le_rfl⟩
  · intro _ x hx
    simp only [Contains, Option.some.injEq] at hx
    rcases hx with ⟨a, b, rfl, rfl, hl, hu⟩
    exact ⟨(by linarith), hu⟩
  · norm_num [run, rmul_point, rdiv_point, radd_eq, rsub_eq]
  · exact ⟨1, 1, rfl, rfl, le_rfl, le_rfl⟩

/-- Nonsingleton control: dependency overestimation is explicit, not hidden in
an incorrect claim that the analytic point error bounds the output width. -/
theorem composed_unit_interval {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Contains some (⟨-841/5040, 121/120⟩ : Bounds ℝ) (Real.sin x) := by
  refine run_encloses radd_sound rsub_sound rmul_sound rdiv_sound
    (supported := fun _ => true) (zero := 0) rfl
    (six := ⟨6, 6⟩) (oneTwenty := ⟨120, 120⟩) (fiveThousandForty := ⟨5040, 5040⟩)
    (I := ⟨0, 1⟩) ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨6, 6, rfl, rfl, le_rfl, le_rfl⟩
  · exact ⟨120, 120, rfl, rfl, le_rfl, le_rfl⟩
  · exact ⟨5040, 5040, rfl, rfl, le_rfl, le_rfl⟩
  · intro _ y hy
    simp only [Contains, Option.some.injEq] at hy
    rcases hy with ⟨a, b, rfl, rfl, hl, hu⟩
    exact ⟨hl, hu⟩
  · norm_num [run, rmul_unit, rdiv_unit, radd_eq, rsub_eq]
  · exact ⟨0, 1, rfl, rfl, hx0, hx1⟩

/-- Analytic end-to-end control at the largest supported input. -/
theorem at_one : (4241 : ℝ)/5040 ≤ Real.sin 1 ∧ Real.sin 1 ≤ 101/120 := by
  have h := SineTaylor.bounds (x := 1) (by norm_num) (by norm_num)
  norm_num [SineTaylor.polynomial] at h ⊢
  exact h

theorem at_half : (309287 : ℝ)/645120 ≤ Real.sin (1/2) ∧
    Real.sin (1/2) ≤ 1841/3840 := by
  have h := SineTaylor.bounds (x := 1/2) (by norm_num) (by norm_num)
  norm_num [SineTaylor.polynomial] at h ⊢
  exact h

theorem approximation_budget : (1 : ℝ)/5040 < 1/5000 := by norm_num

/-- Unsupported input is unknown even though mathematical sine is defined. -/
theorem unsupported {F : Type} (a s m d : Bounds F → Bounds F → Option (Bounds F))
    (z : F) (six c e i : Bounds F) :
    run (m := Id) (fun _ => false) a s m d z six c e i = none := by
  simp [run]

theorem failed_multiplication {F : Type}
    (a s d : Bounds F → Bounds F → Option (Bounds F))
    (z : F) (six c e i : Bounds F) :
    run (m := Id) (fun _ => true) a s (fun _ _ => none) d z six c e i = none := by
  simp [run]

theorem failed_division {F : Type}
    (z : F) (six c e i : Bounds F) :
    run (m := Id) (fun _ => true) (fun a _ => some a) (fun a _ => some a)
      (fun a _ => some a) (fun _ _ => none) z six c e i = none := by
  simp [run]

def Restricted (allowed : Bool) (_ : Unit) (w x : ℝ) : Prop :=
  allowed = true ∧ x = w

theorem holes_preserved (w : ℝ) :
    ¬ ∃ z, SinValues (Restricted false) () w z := by
  simp [sinValues_defined_iff, Restricted]

theorem outside_support_still_defined :
    ∃ z, SinValues (Restricted true) () 2 z := by
  simp [sinValues_defined_iff, Restricted]

theorem same_witness {w z : ℝ} (h : SinValues (Restricted true) () w z) :
    z = Real.sin w := by
  rcases h with ⟨x, ⟨_, rfl⟩, rfl⟩
  rfl

end GeneralizedIntervalArithmetic.HardwareSineChecks
#audit_namespace GeneralizedIntervalArithmetic.HardwareSineChecks
