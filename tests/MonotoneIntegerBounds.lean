import MonotoneIntegerBounds
import SemanticContinuity
import AuditPolicy

namespace GeneralizedIntervalArithmetic.IntegerBoundChecks

def sourceInput : QInterval := ⟨14/10, 72/10, by norm_num⟩
def negative : QInterval := ⟨-19/10, -11/10, by norm_num⟩
def unit : QInterval := ⟨0, 1, by norm_num⟩

theorem source_floor : sourceInput.floor.lo = 1 ∧ sourceInput.floor.hi = 7 := by
  norm_num [sourceInput, QInterval.floor]
theorem negative_floor_ceil : negative.floor.lo = -2 ∧ negative.floor.hi = -2 ∧
    negative.ceil.lo = -1 ∧ negative.ceil.hi = -1 := by
  norm_num [negative, QInterval.floor, QInterval.ceil]
theorem floor_closed_boundary :
    (QInterval.mk (9/10) 1 (by norm_num)).floor.hi = 1 := by
  norm_num [QInterval.floor]
theorem ceil_closed_boundary :
    (QInterval.mk 1 (11/10) (by norm_num)).ceil.lo = 1 := by
  norm_num [QInterval.ceil]
theorem integer_singleton : (QInterval.point (-2)).floor.lo = -2 ∧
    (QInterval.point (-2)).ceil.hi = -2 := by
  norm_num [QInterval.floor, QInterval.ceil, QInterval.point]

-- Interval precision is not discrete-image exactness.
theorem floor_ne_half (x : ℝ) : (⌊x⌋ : ℝ) ≠ 1/2 := by
  intro h
  have hp : (0 : ℤ) < ⌊x⌋ := by
    exact_mod_cast (show (0 : ℝ) < (⌊x⌋ : ℝ) by rw [h]; norm_num)
  have hn : ⌊x⌋ < (1 : ℤ) := by
    exact_mod_cast (show (⌊x⌋ : ℝ) < (1 : ℝ) by rw [h]; norm_num)
  omega

theorem range_is_not_image : unit.floor.Contains (1/2) ∧
    ¬ ∃ x : ℝ, unit.Contains x ∧ (⌊x⌋ : ℝ) = 1/2 := by
  constructor
  · norm_num [unit, QInterval.floor, QInterval.Contains]
  · rintro ⟨x, _, h⟩; exact floor_ne_half x h

-- Sound monotone bounds do not supply a continuity certificate.
theorem floor_not_continuous :
    ¬ ContinuousOn (fun x : ℝ => (⌊x⌋ : ℝ)) (Set.Icc 0 1) := by
  intro h
  have hc : ContinuousOn (fun x : ℝ => (⌊x⌋ : ℝ) - 1/2) (Set.Icc 0 1) :=
    h.sub continuousOn_const
  obtain ⟨x, _, hx⟩ := certified_curve_zero
    (L := .point (-1/2)) (U := .point (1/2)) hc
    (by norm_num [QInterval.Contains, QInterval.point])
    (by norm_num [QInterval.Contains, QInterval.point])
    (by norm_num [QInterval.point]) (by norm_num [QInterval.point])
  exact floor_ne_half x (by linarith)

-- Reuse the old whole-box result without assuming continuity.
theorem floor_ceil_empty_box :
    ¬ ∃ x y : ℝ, negative.Contains x ∧ negative.Contains y ∧
      (⌊x⌋ : ℝ) + (⌈y⌉ : ℝ) = 0 := by
  apply empty_pixel_sound (R := negative.floor.add negative.ceil)
  · intro x y hx hy
    exact add_encloses (floor_encloses hx) (ceil_encloses hy)
  · norm_num [negative, QInterval.floor, QInterval.ceil, QInterval.add, classify]

-- The antitone contract works with endpoint enclosures too.
theorem reflect_enclosure {x : ℝ} (hx : unit.Contains x) : unit.neg.Contains (-x) := by
  apply antitone_endpoint_encloses (f := fun x => -x) _ _ _ hx
  · intro a _ b _ h; exact neg_le_neg h
  · norm_num [unit, QInterval.neg]
  · norm_num [unit, QInterval.neg]

end GeneralizedIntervalArithmetic.IntegerBoundChecks
#audit_namespace GeneralizedIntervalArithmetic.IntegerBoundChecks
