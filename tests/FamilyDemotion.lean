import FamilyDemotion
import AuditPolicy

namespace GeneralizedIntervalArithmetic.FamilyDemotionChecks
open FamilyDemotion

def seed : LinearInterval := .exact ⟨0,1⟩

theorem seed_fiber (t z : ℝ) : seed.Contains t z ↔ z = t := by
  simpa [seed,QAffine.value] using linear_exact_contains (QAffine.mk 0 1) t z

theorem constant_projection_loses_parameter :
    seed.hull.Contains 1 ∧ ¬ seed.Contains 0 1 := by
  constructor
  · norm_num [seed,LinearInterval.hull,LinearInterval.exact,QInterval.Contains]
  · rw [seed_fiber]; norm_num

theorem correlated_cancel (t z : ℝ) : (seed.sub seed).Contains t z ↔ z = 0 :=
  linear_exact_cancel ⟨0,1⟩ t z

theorem forgetting_before_subtraction_is_loose :
    (seed.hull.sub seed.hull).Contains 1 ∧ ¬ (seed.sub seed).Contains 0 1 := by
  constructor
  · norm_num [seed,LinearInterval.hull,LinearInterval.exact,QInterval.sub,QInterval.Contains]
  · rw [correlated_cancel]; norm_num

theorem restricted_domain_loss :
    (∀ z, (∃ t ∈ ({(1/2:ℝ)} : Set ℝ), seed.Contains t z) ↔ z = 1/2) ∧
    seed.hull.Contains 1 := by
  constructor
  · intro z
    simp [seed_fiber]
  · norm_num [seed,LinearInterval.hull,LinearInterval.exact,QInterval.Contains]

theorem parameter_guard_needed : seed.Contains 2 2 ∧ ¬ seed.hull.Contains 2 := by
  constructor
  · exact (seed_fiber 2 2).mpr rfl
  · norm_num [seed,LinearInterval.hull,LinearInterval.exact,QInterval.Contains]

/-- Numeric outward containment does not imply nonempty domain or exactness. -/
theorem empty_can_be_widened :
    (∅ : Set ℝ) ⊆ ExtendedImageHull.interval 0 1 ∧
    (ExtendedImageHull.interval 0 1).Nonempty ∧
    ¬ (∅ : Set ℝ).Nonempty := by
  exact ⟨Set.empty_subset _,⟨0,by norm_num [ExtendedImageHull.interval]⟩,Set.not_nonempty_empty⟩

/-- Endpoint checks certify affine bounds, not arbitrary functions. -/
theorem nonlinear_endpoint_checks_insufficient :
    (0:ℝ)*(1-0) ≤ 0 ∧ 1*(1-1) ≤ (0:ℝ) ∧
    ¬ (∀ t ∈ Set.Icc (0:ℝ) 1, t*(1-t) ≤ 0) := by
  norm_num
  exact ⟨1/2,by norm_num,by norm_num,by norm_num⟩

theorem unbounded_not_finite :
    ¬ ∃ I : QInterval, ∀ z : ℝ, I.Contains z := by
  rintro ⟨I,h⟩
  have hh := (h ((I.hi:ℝ)+1)).2
  linarith

theorem exact_constant_embedding (I : QInterval) :
    ∀ t z, (LinearInterval.constant I).Contains t z ↔ I.Contains z :=
  linear_constant_contains I

end GeneralizedIntervalArithmetic.FamilyDemotionChecks
#audit_namespace GeneralizedIntervalArithmetic.FamilyDemotionChecks
