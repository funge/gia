import TrackingCertificates
import SemanticContinuity
import AuditPolicy

namespace GeneralizedIntervalArithmetic.PropertyCompositionChecks

/-- Unary specialization of thesis p.37's checkable continuity predicate.
The Boolean child flag is represented propositionally. -/
def CheckContinuous (g : ℝ → ℝ) (x : ℝ) (b : Prop) : Prop := ContinuousAt g x ∧ b

/-- The ordinary sufficient composition rule runs from recursive checks to
continuity of the composite, with the original leaf flag preserved. -/
theorem recursive_checks_suffice (g h : ℝ → ℝ) (x : ℝ) (b : Prop)
    (hc : CheckContinuous g (h x) (CheckContinuous h x b)) :
    CheckContinuous (g ∘ h) x b :=
  ⟨hc.1.comp hc.2.1,hc.2.2⟩

noncomputable def jump (x : ℝ) : ℝ := if x < 1/2 then -1 else 1

theorem jump_no_zero : ¬ ∃ x, jump x = 0 := by
  rintro ⟨x,h⟩
  unfold jump at h
  split at h <;> norm_num at h

/-- Independently derive discontinuity from the intermediate-value theorem. -/
theorem jump_not_continuousOn : ¬ ContinuousOn jump (Set.Icc (0:ℝ) 1) := by
  intro h
  obtain ⟨t,ht,hz⟩ := certified_curve_zero (L := .point (-1)) (U := .point 1) h
    (by norm_num [jump,QInterval.point,QInterval.Contains])
    (by norm_num [jump,QInterval.point,QInterval.Contains]) (by norm_num [QInterval.point])
    (by norm_num [QInterval.point])
  exact jump_no_zero ⟨t,hz⟩

theorem jump_has_discontinuous_point :
    ∃ x ∈ Set.Icc (0:ℝ) 1, ¬ ContinuousAt jump x := by
  by_contra! h
  exact jump_not_continuousOn (fun x hx => (h x hx).continuousWithinAt)

/-- Constant outer functions hide discontinuity in their arguments. Hence the
literal reverse direction printed on p.36 does not hold for ordinary continuity. -/
theorem printed_weak_direction_counterexample :
    ∃ x ∈ Set.Icc (0:ℝ) 1,
      CheckContinuous ((fun _ : ℝ => (0:ℝ)) ∘ jump) x True ∧
      ¬ CheckContinuous (fun _ : ℝ => (0:ℝ)) (jump x)
        (CheckContinuous jump x True) := by
  obtain ⟨x,hx,hn⟩ := jump_has_discontinuous_point
  exact ⟨x,hx,⟨continuousAt_const,trivial⟩,fun h => hn h.2.1⟩

/-- The obstruction already uses total real functions and true leaf flags;
partiality and floating-point behavior are not involved. -/
theorem constant_composite (x : ℝ) : ((fun _ : ℝ => (0:ℝ)) ∘ jump) x = 0 := rfl

theorem square_jump (x : ℝ) : (jump x)^2 = 1 := by
  unfold jump
  split <;> norm_num

/-- Nonconstant outer operation: cancellation of the jump is not limited to
constant functions. The existing source-arrow counterexample is preserved. -/
theorem square_masks_discontinuity :
    (∃ a b : ℝ, a^2 ≠ b^2) ∧
    ∃ x ∈ Set.Icc (0:ℝ) 1,
      CheckContinuous ((fun t : ℝ => t^2) ∘ jump) x True ∧
      ¬ CheckContinuous (fun t : ℝ => t^2) (jump x) (CheckContinuous jump x True) := by
  refine ⟨⟨0, 1, by norm_num⟩, ?_⟩
  obtain ⟨x, hx, hn⟩ := jump_has_discontinuous_point
  have he : (fun t : ℝ => t^2) ∘ jump = fun _ => (1:ℝ) := funext square_jump
  refine ⟨x, hx, ?_, fun h => hn h.2.1⟩
  rw [he]
  exact ⟨continuousAt_const, trivial⟩

/-- Actual semantic continuity can be true when the recursive certificate is
false. Keeping its possible=false bit would make the property description wrong. -/
theorem masked_check_requires_unknown :
    ∃ x ∈ Set.Icc (0:ℝ) 1,
      let C := CheckContinuous (fun t : ℝ => t^2) (jump x) (CheckContinuous jump x True)
      let P := CheckContinuous ((fun t : ℝ => t^2) ∘ jump) x True
      ¬ C ∧ P ∧
      ¬ (DomainConstraints.exactDomain (fun _ : Unit => C)).Compatible () P ∧
      (TrackingCertificates.sufficient (DomainConstraints.exactDomain (fun _ : Unit => C))).Compatible () P := by
  obtain ⟨x, hx, hp, hn⟩ := square_masks_discontinuity.2
  refine ⟨x, hx, hn, hp, fun h => hn (h.2 hp), ?_⟩
  exact TrackingCertificates.sufficient_compatible ⟨id, id⟩
    (fun hc => recursive_checks_suffice _ _ _ _ hc)

end GeneralizedIntervalArithmetic.PropertyCompositionChecks
#audit_namespace GeneralizedIntervalArithmetic.PropertyCompositionChecks
