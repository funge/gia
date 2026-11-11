import SineQuadrants
import AuditPolicy

namespace GeneralizedIntervalArithmetic.CosineQuadrantChecks
open HardwareAddition HardwareSine HardwareQuadrants

noncomputable def rlt (a b : ℝ) : Bool := by classical exact decide (a < b)
noncomputable def call (a b : ℝ) : Option (ℝ × ℝ) := some (a*b,a*b)
noncomputable def mul (I J : Bounds ℝ) :=
  HardwareMultiplication.assembleFour min max
    (call I.lo J.lo) (call I.lo J.hi) (call I.hi J.lo) (call I.hi J.hi)
noncomputable def sub (I J : Bounds ℝ) : Option (Bounds ℝ) := some ⟨I.lo-J.hi,I.hi-J.lo⟩
noncomputable def wide (_ : Bounds ℝ) : Option (Bounds ℝ) := some ⟨-1,1⟩

theorem mul_sound : OpSound some mul (· * ·) := by
  apply mul_op_sound
  · simp [HardwareMultiplication.SelectSound]
  · simp [HardwareMultiplication.SelectSound]
  · simp [HardwareMultiplication.CallSound,call]

theorem sub_sound : OpSound some sub (· - ·) := by
  intro I J O x y hr hx hy
  cases hr
  rcases hx with ⟨a,b,ha,hb,hl,hu⟩
  rcases hy with ⟨c,d,hc,hd,jl,ju⟩
  simp only [Option.some.injEq] at ha hb hc hd
  subst a; subst b; subst c; subst d
  exact ⟨_,_,rfl,rfl,sub_le_sub hl ju,sub_le_sub hu jl⟩

theorem wide_sin : RangeSound some wide := by
  intro I O x hr _
  cases hr
  exact ⟨-1,1,rfl,rfl,Real.neg_one_le_sin x,Real.sin_le_one x⟩

theorem wide_cos : ∀ I O x, wide I = some O → Contains some I x → Contains some O (Real.cos x) := by
  intro I O x hr _
  cases hr
  exact ⟨-1,1,rfl,rfl,Real.neg_one_le_cos x,Real.cos_le_one x⟩

theorem mul_exists (I J : Bounds ℝ) : ∃ K, mul I J = some K := ⟨_,rfl⟩

theorem evaluate_wide (c : Cell ℝ) (I P : Bounds ℝ) :
    evaluate (m := Id) mul sub wide wide 0 P c I = some ⟨-1,1⟩ := by
  obtain ⟨M,hM⟩ := mul_exists ⟨c.coefficient,c.coefficient⟩ P
  have hsub : sub I M = some (⟨I.lo-M.hi,I.hi-M.lo⟩ : Bounds ℝ) := rfl
  simp only [evaluate,hM,bind,pure,hsub]
  cases c.mode <;> norm_num [wide,sub]

/-- Independent exact-real client executes clipping, all seven shifts, both
kernel branches, reflection, and hulling. Coarse kernels isolate composition. -/
theorem full_pipeline {x : ℝ} (hx : -4 ≤ x ∧ x ≤ 4) :
    Contains some (⟨-1,1⟩ : Bounds ℝ) (Real.sin x) := by
  apply quadrants_enclose (lt := rlt) (mn := min) (mx := max)
    (by simp [HardwareDivision.CompareSound,rlt])
    (by simp [HardwareMultiplication.SelectSound])
    (by simp [HardwareMultiplication.SelectSound]) mul_sound sub_sound wide_sin wide_cos
    (v := markValue) (by intro m; rfl) (P := ⟨Real.pi,Real.pi⟩)
    (I := ⟨-4,4⟩) (hp := ⟨Real.pi,Real.pi,rfl,rfl,le_rfl,le_rfl⟩)
  · norm_num [HardwareQuadrants.run,pieces,clip,hullList,hull,unitGuard,table,markValue,rlt,evaluate_wide]
  · exact ⟨-4,4,rfl,rfl,hx.1,hx.2⟩

theorem cosine_at_one : (389:ℝ)/720 ≤ Real.cos 1 ∧ Real.cos 1 ≤ 21785/40320 := by
  have h := CosineTaylor.bounds (x := 1) (by norm_num) (by norm_num)
  norm_num [CosineTaylor.polynomial] at h ⊢
  exact h

/-- Endpoints alone miss the interior maximum of cosine on [-1,1]. -/
theorem cosine_endpoints_miss_maximum :
    ¬ Real.cos 0 ≤ max (Real.cos (-1)) (Real.cos 1) := by
  simp only [Real.cos_zero,Real.cos_neg,max_self]
  have h := cosine_at_one.2
  norm_num at h ⊢
  linarith

theorem analytic_budget : (1:ℝ)/40320 < 1/40000 := by norm_num

theorem boundaries_covered (x : ℝ) (hx : -4 ≤ x ∧ x ≤ 4) :
    ∃ c ∈ table markValue, Contains some c.domain x := table_cover (by intro _; rfl) hx

theorem late_failure : HardwareQuadrants.run (m := Id) (fun _ => true)
    (fun a b : Nat => decide (a < b)) min max
    (fun c _ => if c.coefficient = 0 then some (⟨0,1⟩ : Bounds Nat) else none)
    [⟨⟨0,1⟩,0,.sin⟩,⟨⟨1,2⟩,1,.cos⟩] ⟨0,2⟩ = none := by
  norm_num [HardwareQuadrants.run,pieces,clip]

theorem failed_cosine {F : Type} (add sub mul : Bounds F → Bounds F → Option (Bounds F))
    (mn : F → F → F) (z o : F) (two a b c I : Bounds F)
    (h : mul I I = none) :
    HardwareCosine.run (m := Id) (fun _ => true) add sub mul (fun _ _ => none)
      mn z o two a b c I = none := by
  simp [HardwareCosine.run,h]

theorem external_hole :
    ¬ ∃ z, SinValues (fun (_ : Unit) (_ x : ℝ) => x ≠ 0 ∧ x = 0) () 0 z := by
  simp [sinValues_defined_iff]

end GeneralizedIntervalArithmetic.CosineQuadrantChecks
#audit_namespace GeneralizedIntervalArithmetic.CosineQuadrantChecks
