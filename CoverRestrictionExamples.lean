import CoverRestriction
import CoverPresence
import ConditionalCoverExamples

namespace GeneralizedIntervalArithmetic.CoverRestrictionExamples

def ascending : LinearInterval := .exact ⟨0,1⟩
def descending : LinearInterval := .exact ⟨1,0⟩
def alternatives : FiniteLinearCover := [ascending,descending]
def everywhere := MultiplicationExamples.everywhere
def Values (t z : ℝ) := t ∈ Set.Icc (0:ℝ) 1 ∧ (z = t ∨ z = 1-t)

theorem alternatives_sound : alternatives.SoundOn everywhere Values := by
  refine ⟨?_,fun _ _ h => ⟨h.1,trivial⟩,fun t h => ⟨t,h.1,Or.inl rfl⟩⟩
  rintro t z ⟨_,hz⟩
  rcases hz with hz | hz
  · subst z
    refine ⟨ascending,by simp [alternatives],?_⟩
    simp [ascending,LinearInterval.Contains,LinearInterval.exact,QAffine.value]
  · subst z
    refine ⟨descending,by simp [alternatives],?_⟩
    simp [descending,LinearInterval.Contains,LinearInterval.exact,QAffine.value]

def center : ParameterCell := ⟨⟨2/5,3/5,by norm_num⟩,by norm_num,by norm_num⟩
def fine : FiniteLinearCover := (alternatives.reparam center).coalesce
def coarse : FiniteLinearCover := alternatives.coalesce.reparam center
def LocalValues (s z : ℝ) := s ∈ Set.Icc (0:ℝ) 1 ∧ Values (center.map s) z

theorem fine_contract : fine.SoundOn (center.pullDomain everywhere) LocalValues :=
  cover_coalesce_domain_sound (cover_reparam_domain_sound alternatives_sound center)

theorem coarse_contract : coarse.SoundOn (center.pullDomain everywhere) LocalValues :=
  cover_reparam_domain_sound (cover_coalesce_domain_sound alternatives_sound) center

theorem fine_coefficients : fine.map (fun I => (I.lower,I.upper)) =
    [(⟨2/5,2/5⟩,⟨3/5,3/5⟩)] := by decide +kernel

theorem coarse_coefficients : coarse.map (fun I => (I.lower,I.upper)) =
    [(⟨0,0⟩,⟨1,1⟩)] := by decide +kernel

theorem coarse_spurious_value : ∃ I ∈ coarse, I.Contains (1/2) (9/10) := by
  refine ⟨(ascending.join descending).reparam center,?_,?_⟩
  · simp [coarse,alternatives,FiniteLinearCover.coalesce,FiniteLinearCover.joinFrom,
      FiniteLinearCover.reparam]
  · norm_num [ascending,descending,LinearInterval.Contains,LinearInterval.reparam,
      LinearInterval.join,LinearInterval.exact,QAffine.reparam,QAffine.value,center]

theorem coalescing_order_loses_information : ¬ coarse.IncludedIn fine := by
  intro h
  obtain ⟨I,hi,hI⟩ := h (1/2) (by norm_num) (9/10) coarse_spurious_value
  have he : I = (ascending.reparam center).join (descending.reparam center) := by
    simpa [fine,alternatives,FiniteLinearCover.reparam,FiniteLinearCover.coalesce,
      FiniteLinearCover.joinFrom] using hi
  subst I
  norm_num [ascending,descending,LinearInterval.Contains,LinearInterval.reparam,
    LinearInterval.join,LinearInterval.exact,QAffine.reparam,QAffine.value,center] at hI

theorem fine_reciprocal_succeeds : fine.recip?.isSome := by decide +kernel

theorem coarse_reciprocal_unknown : coarse.recip?.isNone := by decide +kernel

def reciprocal : FiniteLinearCover := fine.recip?.get fine_reciprocal_succeeds

theorem reciprocal_contract : reciprocal.SoundOn (center.pullDomain everywhere)
    (QuotientValues (fun _ z => z = 1) LocalValues) :=
  cover_recip_domain_sound fine_contract (Option.some_get fine_reciprocal_succeeds).symm

theorem reciprocal_has_actual_value :
    ∃ z, QuotientValues (fun _ z => z = 1) LocalValues 0 z := by
  exact cover_domain_definite reciprocal_contract (by norm_num) trivial

theorem two_actual_values : LocalValues 0 (2/5) ∧ LocalValues 0 (3/5) := by
  norm_num [LocalValues,Values,center,ParameterCell.map]

theorem no_single_representative :
    ¬ ∃ g : ℝ → ℝ, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ z, LocalValues s z → z = g s := by
  rintro ⟨g,hg⟩
  have ha := hg 0 (by norm_num) (2/5) two_actual_values.1
  have hb := hg 0 (by norm_num) (3/5) two_actual_values.2
  linarith

def midpoint : ParameterCell := ⟨⟨1/2,1/2,le_rfl⟩,by norm_num,by norm_num⟩
def holeDomain : DomainBounds ℝ := everywhere.inter
  ⟨fun t => t ≠ (1/2:ℝ),fun t => t ≠ (1/2:ℝ),fun _ h => h⟩
def HoleValues (t z : ℝ) := t ≠ (1/2:ℝ) ∧ Values t z

theorem midpoint_map (s : ℝ) : midpoint.map s = 1/2 := by
  simp [ParameterCell.map,midpoint]
  ring

theorem degenerate_hole_contract :
    (alternatives.reparam midpoint).SoundOn (midpoint.pullDomain holeDomain)
      (fun s z => s ∈ Set.Icc (0:ℝ) 1 ∧ HoleValues (midpoint.map s) z) :=
  cover_reparam_domain_sound
    (cover_domain_restrict alternatives_sound (fun t => t ≠ (1/2:ℝ))) midpoint

theorem degenerate_hole_has_no_value (s : ℝ) :
    ¬ ∃ z, s ∈ Set.Icc (0:ℝ) 1 ∧ HoleValues (midpoint.map s) z := by
  apply cover_domain_absent degenerate_hole_contract
  intro h
  exact h.2 (midpoint_map s)

def rightCell : ParameterCell := ⟨⟨1/2,1,by norm_num⟩,by norm_num,le_rfl⟩
def selected : FiniteLinearCover := [PiecewiseExamples.constantModel 1]

theorem fresh_right_evaluation :
    evalConditionalCover (ConditionalExamples.inputX.reparam rightCell)
      (ConditionalExamples.inputY.reparam rightCell) ConditionalExamples.jumpTree = some selected := by
  have hc : decideLinearLt (ConditionalExamples.inputX.reparam rightCell) (1/2) = .no := by
    decide +kernel
  simp only [ConditionalExamples.jumpTree,evalConditionalCover,evalGuarded]
  rw [hc]
  rfl

theorem fresh_right_contract : selected.SoundOn
    ((rightCell.pullDomain ConditionalCoverExamples.punctured).inter
      (rightCell.pullDomain MultiplicationExamples.everywhere))
    (fun s z => s ∈ Set.Icc (0:ℝ) 1 ∧ ConditionalCoverExamples.JumpValues (rightCell.map s) z) :=
  evalConditionalCover_reparam_relational_sound rightCell
    ConditionalCoverExamples.punctured_parameter_sound MultiplicationExamples.zero_domain_sound
    fresh_right_evaluation

theorem fresh_boundary_hole :
    ¬ ∃ z, (0:ℝ) ∈ Set.Icc 0 1 ∧ ConditionalCoverExamples.JumpValues (rightCell.map 0) z := by
  apply cover_domain_absent fresh_right_contract
  intro h
  have hn := h.1
  norm_num [ParameterCell.pullDomain,ConditionalCoverExamples.punctured,
    rightCell,ParameterCell.map] at hn

theorem fresh_interior_defined :
    ∃ z, (1/2:ℝ) ∈ Set.Icc 0 1 ∧ ConditionalCoverExamples.JumpValues (rightCell.map (1/2)) z := by
  apply cover_domain_definite fresh_right_contract (by norm_num)
  change rightCell.map (1/2) ≠ (1/2:ℝ) ∧ True
  norm_num [rightCell,ParameterCell.map]

theorem reparam_does_not_prune_branches :
    (ConditionalCoverExamples.jumpCover.reparam rightCell).length = 2 ∧ selected.length = 1 := by
  constructor
  · rw [cover_reparam_length]
    rfl
  · rfl

end GeneralizedIntervalArithmetic.CoverRestrictionExamples
