import ConditionalCovers
import ConditionalExamples

namespace GeneralizedIntervalArithmetic.ConditionalCoverExamples
open ConditionalExamples

def jumpCover : FiniteLinearCover :=
  [PiecewiseExamples.constantModel (-1), PiecewiseExamples.constantModel 1]

theorem jump_evaluates : evalConditionalCover inputX inputY jumpTree = some jumpCover := by
  have hc : decideLinearLt inputX (1/2) = .unknown := by decide +kernel
  simp only [jumpTree, evalConditionalCover, evalGuarded]
  rw [hc]
  rfl

def punctured : DomainBounds ℝ :=
  ⟨fun t => t ≠ (1/2:ℝ), fun t => t ≠ (1/2:ℝ), fun _ h => h⟩
def PuncturedParameter (t z : ℝ) := t ∈ Set.Icc (0:ℝ) 1 ∧ t ≠ (1/2:ℝ) ∧ z = t

theorem punctured_parameter_sound : (inputX.onDomain punctured).Sound PuncturedParameter := by
  refine ⟨?_,fun _ _ h => ⟨h.1,h.2.1⟩,fun t h => ⟨t,h.1,h.2,rfl⟩⟩
  rintro t z ⟨_,_,hz⟩
  subst z
  change inputX.Contains t t
  simp [inputX, LinearInterval.Contains, LinearInterval.exact, QAffine.value]

def JumpValues := ConditionalExpressionValues PuncturedParameter
  MultiplicationExamples.ZeroValue jumpTree

theorem jump_domain_contract :
    jumpCover.SoundOn (punctured.inter MultiplicationExamples.everywhere) JumpValues :=
  evalConditionalCover_relational_sound punctured_parameter_sound
    MultiplicationExamples.zero_domain_sound jump_evaluates

theorem jump_cover_away : ∀ I ∈ jumpCover, I.hull.AwayZero := by
  intro I hi
  rcases List.mem_cons.mp hi with rfl | hi
  · decide +kernel
  · rcases List.mem_singleton.mp hi with rfl
    decide +kernel

theorem jump_no_zero {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : ¬ JumpValues t 0 :=
  cover_excludes_zero (cover_soundOn_covers jump_domain_contract) jump_cover_away ht

theorem reciprocal_succeeds : jumpCover.recip?.isSome := by decide +kernel

def reciprocalCover : FiniteLinearCover := jumpCover.recip?.get reciprocal_succeeds

theorem reciprocal_domain_contract :
    reciprocalCover.SoundOn (punctured.inter MultiplicationExamples.everywhere)
      (QuotientValues (fun _ z => z = 1) JumpValues) :=
  cover_recip_domain_sound jump_domain_contract (Option.some_get reciprocal_succeeds).symm

theorem reciprocal_hole_preserved :
    ¬ ∃ z, QuotientValues (fun _ z => z = 1) JumpValues (1/2) z := by
  apply cover_domain_absent reciprocal_domain_contract
  intro h
  exact h.1 rfl

theorem reciprocal_defined_left :
    ∃ z, QuotientValues (fun _ z => z = 1) JumpValues (1/4) z := by
  apply cover_domain_definite reciprocal_domain_contract
  · norm_num
  · change (1/4:ℝ) ≠ 1/2 ∧ True
    norm_num

theorem reciprocal_defined_right :
    ∃ z, QuotientValues (fun _ z => z = 1) JumpValues (3/4) z := by
  apply cover_domain_definite reciprocal_domain_contract
  · norm_num
  · change (3/4:ℝ) ≠ 1/2 ∧ True
    norm_num

/-- The input-domain hole does not assert that the expression itself is undefined. -/
theorem expression_defined_at_environment_hole : ConditionalValue (1/2) 0 jumpTree 1 := by
  apply ConditionalValue.no Value.x (by norm_num)
  apply ConditionalValue.leaf
  simpa using (Value.const (x := (1/2:ℝ)) (y := (0:ℝ)) 1)

theorem scalar_reciprocal_unknown :
    ((evalConditional inputX inputY jumpTree).bind LinearInterval.recip?).isNone := by
  decide +kernel

theorem known_true_skips_pole : (evalConditionalCover inputX inputY chooseTrue).isSome := by
  decide +kernel

theorem equality_false_skips_pole : (evalConditionalCover inputX inputY chooseFalse).isSome := by
  decide +kernel

theorem unresolved_pole_unknown : (evalConditionalCover inputX inputY unresolvedPartial).isNone := by
  decide +kernel

theorem undefined_guard_unknown : (evalConditionalCover inputX inputY badGuard).isNone := by
  decide +kernel

theorem unknown_still_has_defined_point : ConditionalValue 0 0 unresolvedPartial 7 :=
  ConditionalExamples.unresolved_has_defined_point

theorem zero_leaf_reciprocal_unknown :
    ((evalConditionalCover inputX inputY (.leaf (.const 0))).bind
      FiniteLinearCover.recip?).isNone := by decide +kernel

theorem zero_leaf_defined : ConditionalValue 0 0 (.leaf (.const 0)) 0 := by
  apply ConditionalValue.leaf
  simpa using (Value.const (x := (0:ℝ)) (y := (0:ℝ)) 0)

theorem interpreted_jump_still_discontinuous :
    ¬ ContinuousOn PiecewiseExamples.jump (Set.Icc (0:ℝ) 1) :=
  ConditionalExamples.interpreted_jump_not_continuous

end GeneralizedIntervalArithmetic.ConditionalCoverExamples
