import AffineDemotionLimits
import AuditPolicy

namespace GeneralizedIntervalArithmetic.AffineDemotionLimitsChecks
open AffineDemotionLimits

theorem candidates_cross :
    (0:ℝ) > 2*0-1 ∧ (0:ℝ) < 2*1-1 := by norm_num

theorem no_single_replacement :
    ¬ ∃ m c : ℝ, Minorant m c ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ m*t+c) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, 2*t-1 ≤ m*t+c) := by
  rintro ⟨m,c,h,h0,h1⟩
  exact incompatible_minorants m c h h0 h1

/-- The obstruction concerns affine representation: the actual function is a
perfect pointwise lower bound, and the constant upper bound 1 is available. -/
theorem square_enclosure {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    max 0 (2*t-1) ≤ t^2 ∧ t^2 ≤ 1 := by
  constructor
  · exact max_le (by nlinarith [sq_nonneg t]) (by nlinarith [sq_nonneg (t-1)])
  · nlinarith [ht.1,ht.2]

/-- An affine target does have a greatest affine minorant. -/
theorem affine_target_best (m c : ℝ) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, m*t+c ≤ m*t+c) ∧
    ∀ n d : ℝ, (∀ t ∈ Set.Icc (0:ℝ) 1, n*t+d ≤ m*t+c) →
      ∀ t ∈ Set.Icc (0:ℝ) 1, n*t+d ≤ m*t+c := by
  exact ⟨fun _ _ => le_rfl, fun _ _ h => h⟩
end GeneralizedIntervalArithmetic.AffineDemotionLimitsChecks
#audit_namespace GeneralizedIntervalArithmetic.AffineDemotionLimitsChecks
