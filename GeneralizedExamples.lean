import PartialEnclosures

namespace GeneralizedIntervalArithmetic.GeneralizedExamples

def unit : QInterval := ⟨0, 1, by norm_num⟩
def parameter : QAffine := ⟨0, 1⟩

theorem ordinary_cancel_width : (unit.sub unit).lo = -1 ∧ (unit.sub unit).hi = 1 := by
  decide +kernel

theorem dependent_cancel_exact (t z : ℝ) :
    ((LinearInterval.exact parameter).sub (.exact parameter)).Contains t z ↔ z = 0 :=
  linear_exact_cancel parameter t z

theorem dependent_cancel_hull :
    ((LinearInterval.exact parameter).sub (.exact parameter)).hull.lo = 0 ∧
    ((LinearInterval.exact parameter).sub (.exact parameter)).hull.hi = 0 := by
  decide +kernel

/-- Finite real functional bounds, with an explicit excluded point. This is a
semantic example, not an algorithm computing reciprocal linear bounds. -/
noncomputable def reciprocal : PartialEnclosure ℝ :=
  ⟨⟨fun t => t⁻¹, fun t => t⁻¹⟩,
   ⟨fun t => t ≠ 0, fun t => t ≠ 0, fun _ h => h⟩⟩

def ReciprocalValue (t z : ℝ) : Prop := t ≠ 0 ∧ z = t⁻¹

theorem reciprocal_sound : reciprocal.Sound ReciprocalValue := by
  refine ⟨?_, fun _ _ h => h.1, fun t ht => ⟨t⁻¹, ht, rfl⟩⟩
  rintro t z ⟨_, rfl⟩
  exact ⟨le_rfl, le_rfl⟩

theorem reciprocal_absent_at_zero : ¬ ∃ z, ReciprocalValue 0 z :=
  domain_absent reciprocal_sound (fun h => h rfl)

theorem reciprocal_defined_away {t : ℝ} (ht : t ≠ 0) : ∃ z, ReciprocalValue t z :=
  domain_definite reciprocal_sound ht

noncomputable def jump (t : ℝ) : ℝ := if t < 0 then -1 else 1
noncomputable def jumpEnclosure : PartialEnclosure ℝ :=
  ⟨⟨fun _ => -1, fun _ => 1⟩, ⟨fun _ => True, fun _ => True, fun _ h => h⟩⟩

theorem jump_sound : jumpEnclosure.Sound (fun t z => z = jump t) := by
  refine ⟨?_, fun _ _ _ => trivial, fun t _ => ⟨jump t, rfl⟩⟩
  rintro t z rfl
  change (-1:ℝ) ≤ jump t ∧ jump t ≤ 1
  unfold jump
  split <;> norm_num

theorem jump_opposite_signs : jump (-1) < 0 ∧ 0 < jump 1 := by
  norm_num [jump]

theorem jump_no_zero : ¬ ∃ t, jump t = 0 := by
  rintro ⟨t, ht⟩
  unfold jump at ht
  split at ht <;> norm_num at ht

/-- Unknown domain information is compatible with both absence and existence. -/
noncomputable def uncertain : PartialEnclosure ℝ :=
  ⟨⟨fun _ => 0, fun _ => 0⟩, ⟨fun _ => False, fun _ => True, fun _ h => h.elim⟩⟩

theorem uncertain_empty_sound : uncertain.Sound (fun _ _ => False) := by
  exact ⟨fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ h => h.elim⟩

theorem uncertain_total_sound : uncertain.Sound (fun _ z => z = 0) := by
  refine ⟨?_, fun _ _ _ => trivial, fun _ h => h.elim⟩
  rintro p z rfl
  exact ⟨le_rfl, le_rfl⟩

theorem reciprocal_sum_sound :
    (reciprocal.add reciprocal).Sound (SumValues ReciprocalValue ReciprocalValue) :=
  partial_add_sound reciprocal_sound reciprocal_sound

theorem restricted_jump_sound :
    (jumpEnclosure.restrict (fun t => t ≠ 0)).Sound (fun t z => t ≠ 0 ∧ z = jump t) :=
  restrict_sound jump_sound _

end GeneralizedIntervalArithmetic.GeneralizedExamples
