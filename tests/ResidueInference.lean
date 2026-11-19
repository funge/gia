import ResidueInference
import AuditPolicy

namespace GeneralizedIntervalArithmetic.ResidueInferenceChecks
open ResidueInference

def stride : Expr Unit := .scale 2 (.floor (.atom ()))
def R (_ : Unit) (x z : ℝ) : Prop := z=x

theorem stride_inferred : infer 2 stride = some 0 := by decide

theorem stride_value (x : ℝ) : Value R stride x (2*(⌊x⌋ : ℤ)) :=
  ⟨(⌊x⌋ : ℤ), ⟨x,rfl,rfl⟩,rfl⟩

theorem stride_excludes (x : ℝ) : ¬ ∃ z, Value R stride x z ∧
    (1/2 : ℝ) ≤ z ∧ z ≤ 3/2 :=
  exclude R stride (d := 2) (by norm_num) stride_inferred (by norm_num)

theorem aligned : infer 8 (.add (.scale 8 (.floor (.atom ()))) (.integer 16)) = some 16 := by decide

theorem affine_composed : infer 4 (.sub (.scale (-8) (.floor (.atom ()))) (.integer 3)) = some (-3) := by decide

theorem sum_integer : integer (.add (.floor (.atom ())) (.floor (.atom ()))) = true := rfl

theorem nonintegral_atom_unknown : infer 2 (Expr.scale 2 (.atom ())) = none := by decide

theorem floor_mod_two_unknown : infer 2 (Expr.floor (.atom ())) = none := by decide

theorem undefined_floor : ¬ ∃ z, Value (fun (_ : Unit) (_ : Unit) (_ : ℝ) => False)
    (.floor (.atom ())) () z := by
  rintro ⟨z,x,hx,_⟩; exact hx

theorem undefined_scaled_floor : ¬ ∃ z, Value (fun (_ : Unit) (_ : Unit) (_ : ℝ) => False)
    (.scale 0 (.floor (.atom ()))) () z := by
  rintro ⟨z,x,hx,_⟩
  exact undefined_floor ⟨x,hx⟩

/-- A different term's floor tag cannot be copied to the raw real term. -/
def mixed : Expr Bool := .add (.scale 2 (.floor (.atom false))) (.scale 2 (.atom true))
def mixedR (a : Bool) (_ : Unit) (z : ℝ) := z = if a then 1/2 else 0

theorem mixed_unknown : infer 2 mixed = none ∧ integer mixed = false := by decide

theorem mixed_falsifier : Value mixedR mixed () 1 := by
  refine ⟨0,1, ?_, ?_, by norm_num⟩
  · refine ⟨0, ⟨0, ?_, ?_⟩, by norm_num⟩ <;> norm_num [Value,mixedR]
  · exact ⟨1/2,by norm_num [Value,mixedR],by norm_num⟩

/-- Branch selection is opaque; one integral branch gives no global tag. -/
def branchR (_ : Unit) (p : Bool) (z : ℝ) := z = if p then 1/2 else 0

theorem branch_integral : Value branchR (.atom ()) false 0 := by simp [Value,branchR]
theorem branch_real : Value branchR (.scale 2 (.atom ())) true 1 := by
  exact ⟨1/2,by simp [Value,branchR],by norm_num⟩

theorem branch_unknown : infer 2 (Expr.scale 2 (.atom ())) = none := by decide

theorem external_hole : ¬ ∃ z, Value
    (fun a p z => False ∧ R a p z) stride (0 : ℝ) z := by
  rintro ⟨z,hz⟩
  obtain ⟨x,hx,_⟩ := hz
  obtain ⟨y,hy,_⟩ := hx
  exact hy.1

theorem scaled_inside_floor_unknown : infer 2 (Expr.floor (.scale 2 (.atom ()))) = none := by decide

theorem scaled_inside_floor_attains_one : Value R (.floor (.scale 2 (.atom ()))) (1/2 : ℝ) 1 := by
  refine ⟨1,⟨1/2,rfl,by norm_num⟩,by norm_num⟩

def reciprocal (_ : Unit) (x z : ℝ) := x ≠ 0 ∧ z=1/x

theorem zero_times_floor_pole_tag : infer 2 (Expr.scale 0 (.floor (.atom ()))) = some 0 := by decide

theorem zero_times_floor_pole_undefined : ¬ ∃ z,
    Value reciprocal (.scale 0 (.floor (.atom ()))) (0 : ℝ) z := by
  rintro ⟨z,hz⟩
  obtain ⟨x,hx,_⟩ := hz
  obtain ⟨y,hy,_⟩ := hx
  exact hy.1 rfl

#audit_namespace GeneralizedIntervalArithmetic.ResidueInferenceChecks
end GeneralizedIntervalArithmetic.ResidueInferenceChecks
