import AuditPolicy
import NumberPromotion

namespace GeneralizedIntervalArithmetic.NumberPromotionChecks
open NumberPromotion

theorem control_1 : down ((3 / 2 : ℝ) : EReal) = ((1 : ℝ) : EReal) := by
  change (((⌊(3 / 2 : ℝ)⌋ : ℤ) : ℝ) : EReal) = _
  norm_num
theorem control_2 : up ((-1 / 2 : ℝ) : EReal) = ((0 : ℝ) : EReal) := by
  change (((⌈(-1 / 2 : ℝ)⌉ : ℤ) : ℝ) : EReal) = _
  norm_num
theorem control_3 : down ((-1 / 2 : ℝ) : EReal) = ((-1 : ℝ) : EReal) := by
  change (((⌊(-1 / 2 : ℝ)⌋ : ℤ) : ℝ) : EReal) = _
  norm_num
theorem control_4 : down (⊤ : EReal) = ⊤ ∧ up (⊥ : EReal) = ⊥ := ⟨rfl,rfl⟩
theorem control_5 : hull ∅ = ∅ := empty
theorem control_6 : hull Set.univ = Set.univ := Set.eq_univ_of_univ_subset (sound _)
theorem control_7 : down ((0 : ℝ) : EReal) = 0 ∧ up ((0 : ℝ) : EReal) = 0 :=
  fixed (Or.inr (Or.inr ⟨0, by norm_num⟩))

/-- A genuine loss: the integer enclosure of a half admits zero. -/
theorem control_8 : (0 : ℝ) ∈ hull {1/2} ∧ (0 : ℝ) ∉ ({1/2} : Set ℝ) := by
  constructor
  · change down (ExtendedImageHull.lower {1/2}) ≤ (0 : EReal) ∧
      (0 : EReal) ≤ up (ExtendedImageHull.upper {1/2})
    simp only [ExtendedImageHull.lower, ExtendedImageHull.upper, Set.image_singleton,
      csInf_singleton, csSup_singleton]
    change (((⌊(1/2 : ℝ)⌋ : ℤ) : ℝ) : EReal) ≤ 0 ∧ 0 ≤ (((⌈(1/2 : ℝ)⌉ : ℤ) : ℝ) : EReal)
    norm_num
  · norm_num
theorem control_9 (z : ℤ) : promoteRat z = promoteInt z := promotion_coherent z
theorem control_10 : ExceptionalComparisons.bound .undefined = none := rfl
theorem control_11 : ExceptionalComparisons.bound .negInf = some ⊥ := rfl
theorem control_12 : ExceptionalComparisons.bound .posInf = some ⊤ := rfl
theorem rational_comparison_control :
    ExceptionalComparisons.observe .le (promoteRat (1/2)) (promoteRat 1) = some true ∧
    ExceptionalComparisons.observe .ge (promoteRat (1/2)) (promoteRat 1) = some false := by
  have h := rational_comparisons (1/2) 1
  norm_num at h
  exact ⟨h.2.1, h.2.2.2.1⟩
end GeneralizedIntervalArithmetic.NumberPromotionChecks

#audit_namespace GeneralizedIntervalArithmetic.NumberPromotionChecks
