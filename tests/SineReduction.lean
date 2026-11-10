import SineReduction
import AuditPolicy

namespace GeneralizedIntervalArithmetic.SineReductionChecks
open HardwareAddition HardwareSine

noncomputable def call (a b : ℝ) : Option (ℝ × ℝ) := some (a*b, a*b)
noncomputable def mul (I J : Bounds ℝ) :=
  HardwareMultiplication.assembleFour min max
    (call I.lo J.lo) (call I.lo J.hi) (call I.hi J.lo) (call I.hi J.hi)
noncomputable def sub (I J : Bounds ℝ) : Option (Bounds ℝ) :=
  some ⟨I.lo - J.hi, I.hi - J.lo⟩

noncomputable def kernel (I : Bounds ℝ) : Option (Bounds ℝ) := by
  classical
  exact if I.lo = I.hi then some ⟨Real.sin I.lo, Real.sin I.hi⟩ else none

theorem mul_sound : OpSound some mul (· * ·) := by
  apply mul_op_sound
  · simp [HardwareMultiplication.SelectSound]
  · simp [HardwareMultiplication.SelectSound]
  · simp [HardwareMultiplication.CallSound, call]

theorem sub_sound : OpSound some sub (· - ·) := by
  intro I J O x y hr hx hy
  cases hr
  rcases hx with ⟨a, b, ha, hb, hl, hu⟩
  rcases hy with ⟨c, d, hc, hd, jl, ju⟩
  simp only [Option.some.injEq] at ha hb hc hd
  subst a; subst b; subst c; subst d
  exact ⟨_, _, rfl, rfl, sub_le_sub hl ju, sub_le_sub hu jl⟩

theorem kernel_sound : RangeSound some kernel := by
  intro I O x hr hx
  classical
  simp only [kernel] at hr
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

theorem mul_point (a b : ℝ) : mul ⟨a,a⟩ ⟨b,b⟩ = some ⟨a*b,a*b⟩ := by
  simp [mul, call, HardwareMultiplication.assembleFour]

theorem translated_run (x : ℝ) : reduce (m := Id) mul sub kernel
    ⟨Real.pi, Real.pi⟩ ⟨2,2⟩ ⟨x + 2*Real.pi, x + 2*Real.pi⟩ =
    some ⟨Real.sin x, Real.sin x⟩ := by
  simp [reduce, mul_point, sub, kernel]

/-- Independent real arithmetic exercises the period proof and actual program. -/
theorem translated_enclosure (x : ℝ) :
    Contains some (⟨Real.sin x, Real.sin x⟩ : Bounds ℝ) (Real.sin (x + 2*Real.pi)) := by
  apply reduce_encloses mul_sound sub_sound kernel_sound
    (n := 1) (P := ⟨Real.pi, Real.pi⟩) (C := ⟨2,2⟩)
    (I := ⟨x+2*Real.pi,x+2*Real.pi⟩)
  · exact ⟨_, _, rfl, rfl, le_rfl, le_rfl⟩
  · exact ⟨2, 2, rfl, rfl, by norm_num, by norm_num⟩
  · exact translated_run x
  · exact ⟨_, _, rfl, rfl, le_rfl, le_rfl⟩

theorem exhaustion {F : Type} (m s : Bounds F → Bounds F → Option (Bounds F))
    (k : Bounds F → Option (Bounds F)) (P I : Bounds F) :
    searchPeriods (m := Id) m s k P I [] = none := rfl

theorem failed_shift {F : Type} (s : Bounds F → Bounds F → Option (Bounds F))
    (k : Bounds F → Option (Bounds F)) (P C I : Bounds F) :
    reduce (m := Id) (fun _ _ => none) s k P C I = none := by simp [reduce]

theorem retry_after_failure : searchPeriods (m := Id)
    (fun C _ => if C.lo = 0 then none else some C)
    (fun I _ => some I) (fun I => some I)
    (⟨0,0⟩ : Bounds Nat) ⟨7,8⟩ [⟨0,0⟩,⟨2,2⟩] = some ⟨7,8⟩ := by
  simp [searchPeriods, reduce]

theorem approximate_pi_is_not_exact :
    ¬ Contains some (⟨HardwarePi.lower, HardwarePi.lower⟩ : Bounds ℝ) Real.pi :=
  HardwarePi.lower_singleton_misses

theorem external_hole :
    ¬ ∃ z, SinValues (fun (_ : Unit) (_ x : ℝ) => x ≠ 0 ∧ x = 0) () 0 z := by
  simp [sinValues_defined_iff]

end GeneralizedIntervalArithmetic.SineReductionChecks
#audit_namespace GeneralizedIntervalArithmetic.SineReductionChecks
