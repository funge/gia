import LinearFamilyEquality
import AuditPolicy
namespace GeneralizedIntervalArithmetic.LinearFamilyEqualityChecks
open LinearFamilyEquality FamilyDemotion

theorem constant_exact (I : QInterval) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.constant I).Contains t z ↔
      (LinearInterval.constant (LinearInterval.constant I).hull).Contains t z := by
  apply (hull_fibers_equal_iff _).mpr
  exact ⟨rfl,rfl⟩

theorem range_equality_not_fiber_equality :
    range shrinking = Set.Icc (0:ℝ) 1 ∧
    ¬ (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      shrinking.Contains t z ↔ (LinearInterval.constant shrinking.hull).Contains t z) := by
  refine ⟨shrinking_range, ?_⟩
  rw [hull_fibers_equal_iff]
  norm_num [shrinking]

theorem interior_shared_parameter :
    shrinking.Contains (1/2) (1/8) ∧ ¬ shrinking.Contains (1/2) 0 := by
  norm_num [shrinking,LinearInterval.Contains,QAffine.value]

theorem canonical_counterexample :
    range shrinking = Set.Icc (0:ℝ) 1 ∧
    ¬ (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨0,1⟩).Contains t z → shrinking.Contains t z) ∧
    ¬ (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨1,0⟩).Contains t z → shrinking.Contains t z) :=
  ⟨shrinking_range,shrinking_not_forward,shrinking_not_reverse⟩

/-- Domain restriction and any admitted value witness remain the caller's;
the existing general family theorem is the bridge, not a second implementation. -/
theorem existing_bridge (I : LinearInterval) :
    GeneralFamilyDemotion.Demotes (fun t => {z | I.Contains t z})
      (DomainConstraints.exactDomain (fun t => t ∈ Set.Icc (0:ℝ) 1))
      (fun _ => {z | I.hull.Contains z})
      (DomainConstraints.exactDomain (fun t => t ∈ Set.Icc (0:ℝ) 1)) :=
  GeneralFamilyDemotion.affine_to_constant I

/-- The former counterexample satisfies precisely the added alternative. -/
theorem shrinking_full_endpoint :
    ∀ z, shrinking.Contains 0 z ↔ z ∈ Set.Icc (0:ℝ) 1 := by
  have h := canonical_or_full_fiber_of_range shrinking 0 1 (by norm_num) (by simpa using shrinking_range)
  rcases h with hf | hr | h0 | h1
  · exact False.elim (shrinking_not_forward hf)
  · exact False.elim (shrinking_not_reverse hr)
  · simpa using h0
  · have := (h1 0).mpr (by norm_num)
    norm_num [shrinking,LinearInterval.Contains,QAffine.value] at this

def expanding : LinearInterval := ⟨⟨1/4,0⟩,⟨3/4,1⟩,by norm_num,by norm_num⟩

theorem expanding_full_endpoint :
    (∀ z, expanding.Contains 1 z ↔ z ∈ Set.Icc (0:ℝ) 1) ∧
    ¬ (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨0,1⟩).Contains t z → expanding.Contains t z) ∧
    ¬ (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨1,0⟩).Contains t z → expanding.Contains t z) := by
  constructor
  · intro z; simp [expanding,LinearInterval.Contains,QAffine.value]
  · rw [exact_representative_iff,exact_representative_iff]
    norm_num [expanding]

theorem both_orientations_and_singleton :
    (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨0,1⟩).Contains t z →
        (LinearInterval.exact ⟨0,1⟩).Contains t z) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨1,0⟩).Contains t z →
        (LinearInterval.exact ⟨1,0⟩).Contains t z) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨2,2⟩).Contains t z ↔ z = 2) := by
  refine ⟨fun _ _ _ h => h,fun _ _ _ h => h,?_⟩
  intro t ht z
  rw [linear_exact_contains]
  simp [QAffine.value]
  ring_nf

theorem orientations_not_interchangeable :
    ¬ (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨1,0⟩).Contains t z →
        (LinearInterval.exact ⟨0,1⟩).Contains t z) ∧
    ¬ (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨0,1⟩).Contains t z →
        (LinearInterval.exact ⟨1,0⟩).Contains t z) := by
  rw [exact_representative_iff,exact_representative_iff]
  norm_num [LinearInterval.exact]

/-- A conservative projected enclosure does not identify the actual extrema. -/
theorem loose_enclosure_not_endpoint_identity :
    range (LinearInterval.exact ⟨1/2,1/2⟩) ⊆ Set.Icc (0:ℝ) 1 ∧
    (LinearInterval.exact ⟨1/2,1/2⟩).hull.lo ≠ 0 := by
  constructor
  · rintro z ⟨t,ht,hz⟩
    rw [linear_exact_contains] at hz
    simp only [QAffine.value] at hz
    norm_num at hz
    constructor <;> nlinarith
  · norm_num [LinearInterval.hull,LinearInterval.exact]

end GeneralizedIntervalArithmetic.LinearFamilyEqualityChecks
#audit_namespace GeneralizedIntervalArithmetic.LinearFamilyEqualityChecks
