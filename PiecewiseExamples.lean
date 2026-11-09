import PiecewiseSelection
import Presence

namespace GeneralizedIntervalArithmetic.PiecewiseExamples

def everywhere : DomainBounds ℝ := ⟨fun _ => True,fun _ => True,fun _ h => h⟩
def nowhere : DomainBounds ℝ := ⟨fun _ => False,fun _ => False,fun _ h => h⟩
def constantModel (q : ℚ) : LinearInterval := .exact ⟨q,q⟩
def ConstantValue (q : ℚ) (t z : ℝ) : Prop := t ∈ Set.Icc (0:ℝ) 1 ∧ z = q

theorem constant_model_sound (q : ℚ) :
    ((constantModel q).onDomain everywhere).Sound (ConstantValue q) := by
  refine ⟨?_,fun _ _ h => ⟨h.1,trivial⟩,fun t h => ⟨q,h.1,rfl⟩⟩
  rintro t z ⟨_,rfl⟩
  change (1-t)*(q:ℝ)+t*q ≤ q ∧ (q:ℝ) ≤ (1-t)*q+t*q
  have h : (1-t)*(q:ℝ)+t*q = q := by ring
  simp [h]

theorem undefined_model_sound :
    ((constantModel 0).onDomain nowhere).Sound (fun _ _ => False) :=
  ⟨fun _ _ h => h.elim,fun _ _ h => h.elim,fun _ h => h.2.elim⟩

def parameter : LinearInterval := .exact ⟨0,1⟩

theorem comparison_true : decideLinearLt (constantModel 0) 1 = .yes := by decide +kernel

theorem comparison_equal_false : decideLinearLt (constantModel 1) 1 = .no := by decide +kernel

theorem comparison_lower_boundary_false : decideLinearLt parameter 0 = .no := by decide +kernel

theorem comparison_upper_boundary_unknown : decideLinearLt parameter 1 = .unknown := by decide +kernel

theorem jump_guard_unknown : decideLinearLt parameter (1/2) = .unknown := by decide +kernel

theorem jump_guard_sound : BranchSound (decideLinearLt parameter (1/2)) (fun t => t < (1/2:ℝ)) := by
  have hg : ∀ t ∈ Set.Icc (0:ℝ) 1, parameter.Contains t t := by
    intro t _
    simp [parameter,LinearInterval.Contains,LinearInterval.exact,QAffine.value]
  simpa using (decideLinearLt_sound (1/2:ℚ) hg)

theorem jump_selection_sound :
    ((selectLinear .unknown (constantModel (-1)) (constantModel 1)).onDomain
      (selectDomain .unknown everywhere everywhere)).Sound
      (PiecewiseValues (fun t => t < (1/2:ℝ)) (ConstantValue (-1)) (ConstantValue 1)) := by
  have hg := jump_guard_sound
  rw [jump_guard_unknown] at hg
  exact select_domain_sound hg (constant_model_sound (-1)) (constant_model_sound 1)

theorem jump_bounds :
    (selectLinear .unknown (constantModel (-1)) (constantModel 1)).lower = ⟨-1,-1⟩ ∧
    (selectLinear .unknown (constantModel (-1)) (constantModel 1)).upper = ⟨1,1⟩ := by
  decide +kernel

noncomputable def jump (t : ℝ) : ℝ := if t < 1/2 then -1 else 1

theorem jump_has_piecewise_value {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    PiecewiseValues (fun t => t < (1/2:ℝ)) (ConstantValue (-1)) (ConstantValue 1) t (jump t) := by
  by_cases hp : t < (1/2:ℝ)
  · refine Or.inl ⟨hp,ht,?_⟩
    unfold jump
    rw [if_pos hp]
    norm_num
  · refine Or.inr ⟨hp,ht,?_⟩
    unfold jump
    rw [if_neg hp]
    norm_num

theorem jump_enclosed {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (selectLinear .unknown (constantModel (-1)) (constantModel 1)).Contains t (jump t) :=
  jump_selection_sound.1 t (jump t) (jump_has_piecewise_value ht)

theorem jump_opposite_signs : jump 0 = -1 ∧ jump 1 = 1 := by norm_num [jump]

theorem jump_no_zero : ¬ ∃ t, jump t = 0 := by
  rintro ⟨t,h⟩
  unfold jump at h
  split at h <;> norm_num at h

/-- Directly refutes any accidental continuity conclusion from selection. -/
theorem jump_not_continuous : ¬ ContinuousOn jump (Set.Icc (0:ℝ) 1) := by
  intro hc
  obtain ⟨t,_,hz⟩ := certified_curve_zero (L := .point (-1)) (U := .point 1) hc
    (by norm_num [jump,QInterval.point,QInterval.Contains])
    (by norm_num [jump,QInterval.point,QInterval.Contains])
    (by norm_num [QInterval.point]) (by norm_num [QInterval.point])
  exact jump_no_zero ⟨t,hz⟩

theorem inactive_undefined_branch_sound :
    ((selectLinear .yes (constantModel 7) (constantModel 0)).onDomain
      (selectDomain .yes everywhere nowhere)).Sound
      (PiecewiseValues (fun _ => True) (ConstantValue 7) (fun _ _ => False)) :=
  select_domain_sound (fun _ _ => trivial) (constant_model_sound 7) undefined_model_sound

theorem inactive_undefined_branch_does_not_poison :
    ∃ z, PiecewiseValues (fun _ => True) (ConstantValue 7) (fun _ _ => False) (1/2) z := by
  apply domain_definite inactive_undefined_branch_sound
  change (1/2:ℝ) ∈ Set.Icc 0 1 ∧ True
  norm_num

theorem active_undefined_branch_sound :
    ((selectLinear .no (constantModel 7) (constantModel 0)).onDomain
      (selectDomain .no everywhere nowhere)).Sound
      (PiecewiseValues (fun _ => False) (ConstantValue 7) (fun _ _ => False)) :=
  select_domain_sound (fun _ _ h => h) (constant_model_sound 7) undefined_model_sound

theorem active_undefined_branch_absent :
    ¬ ∃ z, PiecewiseValues (fun _ => False) (ConstantValue 7) (fun _ _ => False) (1/2) z := by
  apply domain_absent active_undefined_branch_sound
  intro h
  exact h.2

theorem unresolved_partial_selection_sound :
    ((selectLinear .unknown (constantModel 7) (constantModel 0)).onDomain
      (selectDomain .unknown everywhere nowhere)).Sound
      (PiecewiseValues (fun t => t < (1/2:ℝ)) (ConstantValue 7) (fun _ _ => False)) :=
  select_domain_sound trivial (constant_model_sound 7) undefined_model_sound

theorem unresolved_partial_domain :
    (selectDomain .unknown everywhere nowhere).possible (1/2) ∧
    ¬ (selectDomain .unknown everywhere nowhere).definite (1/2) := by
  simp [selectDomain,everywhere,nowhere]

/-- The compositional bridge uses the actual guarded interpreter, without a
new Expr conditional or any continuity certificate. -/
theorem interpreted_branch_selection_sound :
    ((selectLinear .unknown (constantModel (-1)) (constantModel 1)).onDomain
      (selectDomain .unknown (everywhere.inter everywhere) (everywhere.inter everywhere))).Sound
      (PiecewiseValues (fun t => t < (1/2:ℝ))
        (ExpressionValues (ConstantValue 1) (ConstantValue 1) (.const (-1)))
        (ExpressionValues (ConstantValue 1) (ConstantValue 1) (.const 1))) :=
  select_guarded_branches_sound trivial (constant_model_sound 1) (constant_model_sound 1) rfl rfl

end GeneralizedIntervalArithmetic.PiecewiseExamples
