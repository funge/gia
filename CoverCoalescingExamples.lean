import CoverCoalescing
import ConditionalCoverExamples
import CoverPresenceExamples

namespace GeneralizedIntervalArithmetic.CoverCoalescingExamples
open ConditionalCoverExamples

theorem limit_two_unchanged : jumpCover.limit 2 = some jumpCover :=
  cover_limit_unchanged (by decide)

theorem limit_one_coalesces : jumpCover.limit 1 = some jumpCover.coalesce := by
  simp [FiniteLinearCover.limit,jumpCover]

theorem bounded_interpreter_pipeline :
    (evalConditionalCover ConditionalExamples.inputX ConditionalExamples.inputY
      ConditionalExamples.jumpTree).bind (FiniteLinearCover.limit 1) =
      some jumpCover.coalesce := by
  rw [jump_evaluates]
  exact limit_one_coalesces

theorem bounded_domain_contract :
    jumpCover.coalesce.SoundOn (punctured.inter MultiplicationExamples.everywhere) JumpValues :=
  cover_limit_domain_sound jump_domain_contract limit_one_coalesces

theorem bounded_output_length : jumpCover.coalesce.length ≤ 1 :=
  cover_limit_length limit_one_coalesces

theorem singleton_scalar_bridge :
    ((PiecewiseExamples.constantModel (-1)).join (PiecewiseExamples.constantModel 1)).onDomain
      (punctured.inter MultiplicationExamples.everywhere) |>.Sound JumpValues :=
  singleton_soundOn_iff.mp bounded_domain_contract

theorem bounded_hole_preserved : ¬ ∃ z, JumpValues (1/2) z := by
  apply cover_domain_absent bounded_domain_contract
  intro h
  exact h.1 rfl

theorem bounded_definite_value : ∃ z, JumpValues (1/4) z := by
  apply cover_domain_definite bounded_domain_contract (by norm_num)
  change (1/4:ℝ) ≠ 1/2 ∧ True
  norm_num

theorem lost_reciprocal_precision : jumpCover.recip?.isSome ∧ jumpCover.coalesce.recip?.isNone := by
  constructor <;> decide +kernel

theorem spurious_range_zero :
    (∃ I ∈ jumpCover.coalesce, I.Contains (1/4) 0) ∧ ¬ JumpValues (1/4) 0 := by
  constructor
  · refine ⟨(PiecewiseExamples.constantModel (-1)).join (PiecewiseExamples.constantModel 1),
      by simp [jumpCover,FiniteLinearCover.coalesce,FiniteLinearCover.joinFrom],?_⟩
    norm_num [LinearInterval.Contains,LinearInterval.join,PiecewiseExamples.constantModel,
      LinearInterval.exact,QAffine.value]
  · exact jump_no_zero (by norm_num)

theorem inclusion_is_strict : ¬ jumpCover.coalesce.IncludedIn jumpCover := by
  intro h
  obtain ⟨I,hi,hI⟩ := h (1/4) (by norm_num) 0 spurious_range_zero.1
  exact awayZero_nonzero (jump_cover_away I hi) (linear_hull_encloses (by norm_num) hI) rfl

theorem zero_limit_unknown : (jumpCover.limit 0).isNone := by decide +kernel

theorem empty_zero_limit_retained : FiniteLinearCover.limit 0 [] = some [] :=
  cover_limit_empty 0

def slopingThree : FiniteLinearCover :=
  [.exact ⟨-2,-1⟩, .exact ⟨2,3⟩, .exact ⟨4,5⟩]

/-- The simple policy coalesces all three members, retaining affine slopes.
It does not claim to choose an optimal two-component representation. -/
theorem three_components_affine_result :
    (slopingThree.limit 2).map (fun C => C.map (fun I => (I.lower,I.upper))) =
      some [(⟨-2,-1⟩,⟨4,5⟩)] := by decide +kernel

/-- Coalescing can preserve a useful certificate as well as losing precision. -/
theorem presence_survives_coalescing :
    ∃ t ∈ Set.Icc (0:ℝ) 1, CoverPresenceExamples.Values t 0 := by
  apply cover_domain_presence
    (cover_coalesce_domain_sound CoverPresenceExamples.domain_contract)
    CoverPresenceExamples.continuous_value_certificate.1
    (fun _ ht _ hz => CoverPresenceExamples.representative_agreement ht hz)
    (fun _ _ => ⟨trivial,trivial⟩)
  · intro I hi
    have he : I = FiniteLinearCover.joinFrom CoverPresenceExamples.L
        [CoverPresenceExamples.L.add CoverPresenceExamples.L] := by
      simpa [CoverPresenceExamples.ranges,FiniteLinearCover.coalesce] using hi
    subst I
    decide +kernel
  · intro I hi
    have he : I = FiniteLinearCover.joinFrom CoverPresenceExamples.L
        [CoverPresenceExamples.L.add CoverPresenceExamples.L] := by
      simpa [CoverPresenceExamples.ranges,FiniteLinearCover.coalesce] using hi
    subst I
    decide +kernel

end GeneralizedIntervalArithmetic.CoverCoalescingExamples
