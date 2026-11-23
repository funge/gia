import StrictComparison
import AuditPolicy

namespace GeneralizedIntervalArithmetic.StrictComparisonChecks
open StrictComparison

def oneThree : QInterval := ⟨1, 3, by norm_num⟩
def fourSix : QInterval := ⟨4, 6, by norm_num⟩
def twoFour : QInterval := ⟨2, 4, by norm_num⟩
def three : QInterval := ⟨3, 3, le_rfl⟩
def unit : QInterval := ⟨0, 1, by norm_num⟩

theorem separated_true : compare oneThree fourSix = .trueOnly := by decide
theorem separated_false : compare fourSix oneThree = .falseOnly := by decide
theorem overlap_both : compare oneThree twoFour = .both := by decide
theorem touching_both : compare oneThree ⟨3, 4, by norm_num⟩ = .both := by decide
theorem reverse_touching_false : compare ⟨3, 4, by norm_num⟩ oneThree = .falseOnly := by decide
theorem equal_singleton_false : compare three three = .falseOnly := by decide
theorem equal_nondegenerate_both : compare unit unit = .both := by decide

theorem overlap_attained :
    true ∈ outcomes oneThree twoFour ∧ false ∈ outcomes oneThree twoFour := by
  constructor
  · rw [true_attainable]; decide
  · rw [false_attainable]; decide

theorem mixed_corner_witnesses :
    (oneThree.Contains oneThree.lo ∧ twoFour.Contains twoFour.hi ∧
      (oneThree.lo : ℝ) < twoFour.hi) ∧
    (oneThree.Contains oneThree.hi ∧ twoFour.Contains twoFour.lo ∧
      (twoFour.lo : ℝ) ≤ oneThree.hi) := both_witnesses overlap_both

theorem singleton_refines_overlap :
    (compare three three).Refines (compare oneThree twoFour) := by
  apply compare_refines
  · intro x hx
    norm_num [QInterval.Contains, three, oneThree] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  · intro x hx
    norm_num [QInterval.Contains, three, twoFour] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]

/-- A shared witness has only false, even though independent unit operands
have both outcomes. Interval equality does not establish independence. -/
noncomputable def correlatedOutcomes : Set Bool := by
  classical
  exact {b | ∃ x : ℝ, unit.Contains x ∧ decide (x < x) = b}

theorem correlated_only_false : correlatedOutcomes = {false} := by
  classical
  ext b
  simp only [correlatedOutcomes, Set.mem_setOf_eq, lt_self_iff_false,
    decide_false, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, _, h⟩; exact h.symm
  · intro h
    refine ⟨0, ?_, h.symm⟩
    norm_num [QInterval.Contains, unit]

theorem correlation_counterexample : outcomes unit unit ≠ correlatedOutcomes := by
  intro h
  have ht : true ∈ outcomes unit unit := by rw [true_attainable]; decide
  rw [h, correlated_only_false] at ht
  simp at ht

theorem information_not_truth_order :
    Truth.falseOnly.Refines .both ∧ Truth.trueOnly.Refines .both ∧
    ¬ Truth.falseOnly.Refines .trueOnly := by
  simp [refines_iff]

theorem right_touch : compare unit ⟨1, 2, by norm_num⟩ = .both := by decide
theorem swapped_right_touch : compare ⟨1, 2, by norm_num⟩ unit = .falseOnly := by decide

/-- A different correlation can remove false rather than true. -/
noncomputable def shiftedOutcomes : Set Bool := by
  classical
  exact {b | ∃ x : ℝ, (⟨0, 2, by norm_num⟩ : QInterval).Contains x ∧
    decide (x < x + 1) = b}

theorem shifted_only_true : shiftedOutcomes = {true} := by
  classical
  ext b
  constructor
  · rintro ⟨x, _, h⟩
    have hx : x < x + 1 := by linarith
    simpa [hx] using h.symm
  · intro h
    have hb : b = true := h
    subst b
    refine ⟨0, ?_, ?_⟩
    · norm_num [QInterval.Contains]
    · norm_num

theorem shifted_marginals_mixed :
    StrictComparison.compare ⟨0, 2, by norm_num⟩ ⟨1, 3, by norm_num⟩ = .both := by decide

theorem shifted_membership (x : ℝ) (hx : (0 : ℝ) ≤ x ∧ x ≤ 2) :
    (⟨0, 2, by norm_num⟩ : QInterval).Contains x ∧
    (⟨1, 3, by norm_num⟩ : QInterval).Contains (x + 1) := by
  norm_num [QInterval.Contains]
  exact ⟨hx, by constructor <;> linarith [hx.1, hx.2]⟩

/-- Both raw separation tests can hold for malformed pairs. They cannot be
constructed as ordered QIntervals and are not inputs to compare. -/
theorem malformed_raw_pairs :
    (0 : ℚ) < 1 ∧ (-1 : ℚ) ≤ 2 ∧ ¬ (2 : ℚ) ≤ 0 ∧ ¬ (1 : ℚ) ≤ -1 := by
  norm_num

end GeneralizedIntervalArithmetic.StrictComparisonChecks
#audit_namespace GeneralizedIntervalArithmetic.StrictComparisonChecks
