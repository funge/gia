import BasicIntervalOps
import AuditPolicy

namespace GeneralizedIntervalArithmetic.BasicOperationChecks

def mixed : QInterval := ⟨-23/10, 31/10, by norm_num⟩
def negative : QInterval := ⟨-4, -2, by norm_num⟩
def positive : QInterval := ⟨2, 4, by norm_num⟩

-- The thesis's printed examples (p. 59, PDF p. 75), with exact decimals.
theorem thesis_negation : positive.neg.lo = -4 ∧ positive.neg.hi = -2 := by
  norm_num [positive, QInterval.neg]
theorem thesis_absolute : mixed.abs.lo = 0 ∧ mixed.abs.hi = 31/10 := by
  norm_num [mixed, QInterval.abs]
theorem negative_absolute : negative.abs.lo = 2 ∧ negative.abs.hi = 4 := by
  norm_num [negative, QInterval.abs]
theorem positive_absolute : positive.abs.lo = 2 ∧ positive.abs.hi = 4 := by
  norm_num [positive, QInterval.abs]
theorem zero_absolute : (QInterval.point 0).abs.lo = 0 ∧
    (QInterval.point 0).abs.hi = 0 := by
  norm_num [QInterval.point, QInterval.abs]

-- Compose the new operations with the existing empty-pixel theorem.
theorem absolute_maximum_excludes_zero :
    ¬ ∃ x y, negative.Contains x ∧ mixed.Contains y ∧ max |x| |y| = 0 := by
  apply empty_pixel_sound (R := negative.abs.maximum mixed.abs)
  · intro x y hx hy
    exact maximum_encloses (abs_encloses hx) (abs_encloses hy)
  · norm_num [classify, negative, mixed, QInterval.abs, QInterval.maximum]

-- Hull may introduce values belonging to neither operand.
theorem hull_is_not_union :
    (negative.hull positive).Contains 0 ∧
    ¬ negative.Contains 0 ∧ ¬ positive.Contains 0 := by
  norm_num [QInterval.Contains, QInterval.hull, negative, positive]

theorem separated_intersection : negative.intersect positive = none := by
  norm_num [QInterval.intersect, negative, positive]

-- A shared endpoint is retained; intersection failure is actual disjointness.
def left : QInterval := ⟨-2, 0, by norm_num⟩
def right : QInterval := ⟨0, 3, by norm_num⟩
theorem shared_boundary : left.intersect right = some (QInterval.point 0) := by
  norm_num [QInterval.intersect, left, right, QInterval.point]
theorem shared_boundary_semantics (x : ℝ) :
    (QInterval.point 0).Contains x ↔ left.Contains x ∧ right.Contains x :=
  intersect_contains_iff shared_boundary x

theorem minimum_endpoint_control :
    (negative.minimum positive).lo = -4 ∧
    (negative.minimum positive).hi = -2 := by
  norm_num [QInterval.minimum, negative, positive]

end GeneralizedIntervalArithmetic.BasicOperationChecks
#audit_namespace GeneralizedIntervalArithmetic.BasicOperationChecks
