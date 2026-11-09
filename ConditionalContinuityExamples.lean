import ConditionalContinuity
import ConditionalExamples

namespace GeneralizedIntervalArithmetic.ConditionalContinuityExamples

def removable : Expr := .div (.sub .x (.const (1/2))) (.sub .x (.const (1/2)))
def removableTree : ConditionalExpr := .iteLt .x (1/2) (.leaf removable) (.leaf (.const 1))

private theorem one_value (t : ℝ) : ConditionalValue t 0 (.leaf (.const 1)) 1 := by
  apply ConditionalValue.leaf
  simpa using (Value.const (x := t) (y := (0:ℝ)) 1)

private theorem removable_left_value (t : ℝ) (ht : t < (1/2:ℝ)) :
    ConditionalValue t 0 (.leaf removable) 1 := by
  have hh : Value t 0 (.const (1/2)) (1/2:ℝ) := by
    simpa using (Value.const (x := t) (y := (0:ℝ)) (1/2))
  have hs := Value.sub Value.x hh
  have hn : t - (1/2:ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_lt ht)
  apply ConditionalValue.leaf
  have hd : Value t 0 removable ((t-(1/2:ℝ))/(t-1/2)) := by
    simpa [removable] using Value.div hs hs hn
  rw [div_self hn] at hd
  exact hd

/-- The true branch has no boundary value; its continuous extension can still
match the false branch selected at equality. -/
theorem removable_certificate :
    ContinuousOn (fun _ : ℝ => (1:ℝ)) (Set.Icc (0:ℝ) 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, ConditionalValue t 0 removableTree 1 := by
  have h := (conditional_threshold_certificate (x := fun t => t) (y := fun _ => 0)
      (f := fun _ => 1) (g := fun _ => 1) (guard := .x)
      (a := .leaf removable) (b := .leaf (.const 1)) (1/2) (by norm_num)
      (fun _ _ => Value.x) continuousOn_const continuousOn_const rfl
      (by intro t _ ht; apply removable_left_value t; norm_num at ht ⊢; exact ht) (fun t _ => one_value t))
  have he : thresholdValue (1/2) (fun _ => 1) (fun _ => 1) = (fun _ : ℝ => (1:ℝ)) := by
    funext t
    simp [thresholdValue]
  rw [he] at h
  exact h

theorem true_branch_undefined_at_boundary :
    ¬ ∃ z, ConditionalValue (1/2) 0 (.leaf removable) z := by
  rintro ⟨z,h⟩
  cases h with
  | leaf h =>
    cases h with
    | div ha hb hn =>
      apply hn
      simpa [Expr.realValue] using value_eq_realValue hb

theorem false_branch_defines_boundary : ConditionalValue (1/2) 0 removableTree 1 :=
  removable_certificate.2 (1/2) (by norm_num)

theorem semantic_certificate_does_not_imply_interpreter_success :
    (evalConditional ConditionalExamples.inputX ConditionalExamples.inputY removableTree).isNone = true := by
  decide +kernel

theorem unmatched_jump_not_continuous :
    ¬ ContinuousOn (thresholdValue (1/2) (fun _ => -1) (fun _ => 1)) (Set.Icc (0:ℝ) 1) := by
  have he : thresholdValue (1/2) (fun _ => -1) (fun _ => 1) = PiecewiseExamples.jump := by
    funext t
    norm_num [thresholdValue,PiecewiseExamples.jump]
  rw [he]
  exact PiecewiseExamples.jump_not_continuous

theorem matching_v_continuous :
    ContinuousOn (thresholdValue (1/2) (fun t => (1/2:ℝ)-t) (fun t => t-(1/2:ℝ)))
      (Set.Icc (0:ℝ) 1) :=
  threshold_continuous (1/2) (by norm_num) _ _
    (continuous_const.sub continuous_id).continuousOn
    (continuous_id.sub continuous_const).continuousOn (by norm_num)

def activeHole : ConditionalExpr :=
  .iteLt .x (1/2) (.leaf (.const 1)) (.leaf ConditionalExamples.pole)

theorem active_boundary_hole : ¬ ∃ z, ConditionalValue (1/2) 0 activeHole z := by
  rintro ⟨z,h⟩
  cases h with
  | yes hg hlt _ => cases hg; norm_num at hlt
  | no _ _ hb =>
    cases hb with
    | leaf hv => exact ConditionalExamples.pole_has_no_value _ _ ⟨z,hv⟩

def guardHole : ConditionalExpr :=
  .iteLt ConditionalExamples.pole (1/2) (.leaf (.const 1)) (.leaf (.const 1))

theorem undefined_guard_not_repaired (t : ℝ) : ¬ ∃ z, ConditionalValue t 0 guardHole z := by
  rintro ⟨z,h⟩
  cases h with
  | yes hg _ _ => exact ConditionalExamples.pole_has_no_value _ _ ⟨_,hg⟩
  | no hg _ _ => exact ConditionalExamples.pole_has_no_value _ _ ⟨_,hg⟩

/- Dedicated positive regression for #28's agreement wrapper. The cells overlap
on [1/4,3/4], and the local functions are distinct in local coordinates. -/
def overlapLeft : ParameterCell := ⟨⟨0,3/4,by norm_num⟩,by norm_num,by norm_num⟩
def overlapRight : ParameterCell := ⟨⟨1/4,1,by norm_num⟩,by norm_num,by norm_num⟩
noncomputable def localRepresentative (C : ParameterCell) (s : ℝ) : ℝ :=
  if C.interval.lo = 0 then (3/2:ℝ)*s+1 else (3/2:ℝ)*s+3/2

theorem overlap_cover : ParameterCover [overlapLeft,overlapRight] := by
  intro t ht
  by_cases h : t ≤ (3/4:ℝ)
  · refine ⟨overlapLeft,by simp,?_⟩
    norm_num [overlapLeft,QInterval.Contains]
    exact ⟨ht.1,h⟩
  · refine ⟨overlapRight,by simp,?_⟩
    norm_num [overlapRight,QInterval.Contains]
    exact ⟨by linarith,ht.2⟩

theorem local_representatives_continuous (C : ParameterCell) (hC : C ∈ [overlapLeft,overlapRight]) :
    ContinuousOn (localRepresentative C) (Set.Icc (0:ℝ) 1) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
  rcases hC with rfl | rfl
  · simpa [localRepresentative,overlapLeft] using
      (((continuous_const.mul continuous_id).add continuous_const :
        Continuous (fun s : ℝ => (3/2:ℝ)*s+1)).continuousOn)
  · unfold localRepresentative
    norm_num [overlapRight]
    exact (((continuous_const.mul continuous_id).add continuous_const :
      Continuous (fun s : ℝ => (3/2:ℝ)*s+3/2)).continuousOn)

/-- Equality on every local parameter, not merely at selected overlap endpoints. -/
theorem full_cell_agreement (C : ParameterCell) (hC : C ∈ [overlapLeft,overlapRight])
    (s : ℝ) : localRepresentative C s = 2*C.map s+1 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
  rcases hC with rfl | rfl <;>
    norm_num [localRepresentative,overlapLeft,overlapRight,ParameterCell.map] <;> ring

theorem local_representatives_distinct : localRepresentative overlapLeft 0 ≠ localRepresentative overlapRight 0 := by
  norm_num [localRepresentative,overlapLeft,overlapRight]

theorem overlap_agreement_wrapper : ContinuousOn (fun t : ℝ => 2*t+1) (Set.Icc (0:ℝ) 1) :=
  parameter_cover_continuous_of_agreement overlap_cover localRepresentative
    local_representatives_continuous (fun C hC s _ => full_cell_agreement C hC s)

end GeneralizedIntervalArithmetic.ConditionalContinuityExamples
