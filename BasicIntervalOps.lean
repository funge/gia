import IntervalOps
import Mathlib.Tactic.Linarith

namespace GeneralizedIntervalArithmetic

/-- Exact finite rational bounds; no empty or infinite endpoints. -/
def QInterval.neg (I : QInterval) : QInterval :=
  ⟨-I.hi, -I.lo, neg_le_neg I.ordered⟩

def QInterval.minimum (I J : QInterval) : QInterval :=
  ⟨min I.lo J.lo, min I.hi J.hi, min_le_min I.ordered J.ordered⟩

def QInterval.maximum (I J : QInterval) : QInterval :=
  ⟨max I.lo J.lo, max I.hi J.hi, max_le_max I.ordered J.ordered⟩

/-- Includes zero in the lower bound exactly when the input straddles zero. -/
def QInterval.abs (I : QInterval) : QInterval :=
  ⟨max 0 (max I.lo (-I.hi)), max (-I.lo) I.hi, by
    have h := I.ordered
    apply max_le
    · rcases le_total 0 I.hi with hp | hn
      · exact hp.trans (le_max_right _ _)
      · exact (by linarith : 0 ≤ -I.lo).trans (le_max_left _ _)
    · exact max_le (h.trans (le_max_right _ _))
        ((neg_le_neg h).trans (le_max_left _ _))⟩

def QInterval.hull (I J : QInterval) : QInterval :=
  ⟨min I.lo J.lo, max I.hi J.hi,
    (min_le_left _ _).trans (I.ordered.trans (le_max_left _ _))⟩

/-- Here `none` means an empty intersection, not an evaluator failure. -/
def QInterval.intersect (I J : QInterval) : Option QInterval :=
  if h : max I.lo J.lo ≤ min I.hi J.hi then
    some ⟨max I.lo J.lo, min I.hi J.hi, h⟩ else none

theorem neg_contains_iff (I : QInterval) (x : ℝ) :
    I.neg.Contains (-x) ↔ I.Contains x := by
  simp [QInterval.Contains, QInterval.neg, and_comm]

theorem minimum_encloses {I J : QInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.minimum J).Contains (min x y) := by
  exact ⟨by simpa [QInterval.minimum] using min_le_min hx.1 hy.1,
    by simpa [QInterval.minimum] using min_le_min hx.2 hy.2⟩

theorem maximum_encloses {I J : QInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.maximum J).Contains (max x y) := by
  exact ⟨by simpa [QInterval.maximum] using max_le_max hx.1 hy.1,
    by simpa [QInterval.maximum] using max_le_max hx.2 hy.2⟩

theorem abs_encloses {I : QInterval} {x : ℝ} (hx : I.Contains x) :
    I.abs.Contains |x| := by
  change ((max 0 (max I.lo (-I.hi)) : ℚ) : ℝ) ≤ |x| ∧
    |x| ≤ ((max (-I.lo) I.hi : ℚ) : ℝ)
  push_cast
  exact ⟨max_le (abs_nonneg _) (max_le (hx.1.trans (le_abs_self _))
    ((neg_le_neg hx.2).trans (neg_le_abs _))),
    abs_le.mpr ⟨by have h := le_max_left (-(I.lo : ℝ)) (I.hi : ℝ); linarith [hx.1],
      hx.2.trans (le_max_right _ _)⟩⟩

theorem hull_encloses {I J : QInterval} {x : ℝ}
    (hx : I.Contains x ∨ J.Contains x) : (I.hull J).Contains x := by
  simp only [QInterval.Contains, QInterval.hull, Rat.cast_min, Rat.cast_max] at *
  rcases hx with h | h
  · exact ⟨(min_le_left _ _).trans h.1, h.2.trans (le_max_left _ _)⟩
  · exact ⟨(min_le_right _ _).trans h.1, h.2.trans (le_max_right _ _)⟩

/-- The hull is the least enclosing interval, not the set-theoretic union. -/
theorem hull_least {I J K : QInterval}
    (hI : ∀ x, I.Contains x → K.Contains x)
    (hJ : ∀ x, J.Contains x → K.Contains x) :
    ∀ x, (I.hull J).Contains x → K.Contains x := by
  have ilo : I.Contains (I.lo : ℝ) := ⟨le_rfl, by exact_mod_cast I.ordered⟩
  have ihi : I.Contains (I.hi : ℝ) := ⟨by exact_mod_cast I.ordered, le_rfl⟩
  have jlo : J.Contains (J.lo : ℝ) := ⟨le_rfl, by exact_mod_cast J.ordered⟩
  have jhi : J.Contains (J.hi : ℝ) := ⟨by exact_mod_cast J.ordered, le_rfl⟩
  intro x hx
  have hl := le_min (hI _ ilo).1 (hJ _ jlo).1
  have hu := max_le (hI _ ihi).2 (hJ _ jhi).2
  have hx' : min (I.lo : ℝ) (J.lo : ℝ) ≤ x ∧
      x ≤ max (I.hi : ℝ) (J.hi : ℝ) := by
    simpa [QInterval.Contains, QInterval.hull] using hx
  exact ⟨hl.trans hx'.1, hx'.2.trans hu⟩

theorem intersect_contains_iff {I J K : QInterval}
    (h : I.intersect J = some K) (x : ℝ) :
    K.Contains x ↔ I.Contains x ∧ J.Contains x := by
  unfold QInterval.intersect at h
  split at h
  · cases h
    simp [QInterval.Contains, max_le_iff, le_min_iff, and_assoc, and_left_comm, and_comm]
  · simp at h

theorem intersect_none_iff (I J : QInterval) :
    I.intersect J = none ↔ ¬ ∃ x : ℝ, I.Contains x ∧ J.Contains x := by
  unfold QInterval.intersect
  split
  · rename_i h
    simp only [reduceCtorEq, false_iff, not_not]
    refine ⟨(max I.lo J.lo : ℚ), ?_⟩
    have h' : max (I.lo : ℝ) (J.lo : ℝ) ≤ min (I.hi : ℝ) (J.hi : ℝ) := by exact_mod_cast h
    simp only [QInterval.Contains, Rat.cast_max]
    exact ⟨⟨le_max_left _ _, h'.trans (min_le_left _ _)⟩,
      ⟨le_max_right _ _, h'.trans (min_le_right _ _)⟩⟩
  · rename_i h
    simp only [true_iff]
    rintro ⟨x, hx, hy⟩
    have h' := (max_le hx.1 hy.1).trans (le_min hx.2 hy.2)
    exact h (by exact_mod_cast h')

end GeneralizedIntervalArithmetic
