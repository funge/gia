import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
Exact interval arithmetic: rational closed intervals denote sets of
real numbers. No connection to the C implementation or floating-point arithmetic
is asserted. An `empty` result is sound; `unknown` makes no existence claim.
-/

namespace GeneralizedIntervalArithmetic

/-- Finite, nonempty closed intervals with exact rational endpoints. -/
structure QInterval where
  lo : ℚ
  hi : ℚ
  ordered : lo ≤ hi

def QInterval.Contains (I : QInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def QInterval.add (I J : QInterval) : QInterval :=
  ⟨I.lo + J.lo, I.hi + J.hi, add_le_add I.ordered J.ordered⟩

def QInterval.sub (I J : QInterval) : QInterval :=
  ⟨I.lo - J.hi, I.hi - J.lo, sub_le_sub I.ordered J.ordered⟩

/-- Every sum of members lies inside the endpoint sum enclosure. -/
theorem add_encloses {I J : QInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.add J).Contains (x + y) := by
  constructor
  · simpa [QInterval.add] using add_le_add hx.1 hy.1
  · simpa [QInterval.add] using add_le_add hx.2 hy.2

/-- Subtraction swaps the second interval's endpoints. -/
theorem sub_encloses {I J : QInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.sub J).Contains (x - y) := by
  constructor
  · simpa [QInterval.sub] using sub_le_sub hx.1 hy.2
  · simpa [QInterval.sub] using sub_le_sub hx.2 hy.1

inductive Classification where
  | empty
  | unknown
  deriving DecidableEq, Repr

/-- Only strict exclusion of zero certifies an equation's region as empty. -/
def classify (I : QInterval) : Classification :=
  if I.hi < 0 ∨ 0 < I.lo then .empty else .unknown

theorem classify_empty_sound {I : QInterval} {z : ℝ}
    (hc : classify I = .empty) (hz : I.Contains z) : z ≠ 0 := by
  have he : I.hi < 0 ∨ 0 < I.lo := by
    by_contra h
    simp [classify, h] at hc
  intro hzero
  subst z
  rcases he with hneg | hpos
  · have h : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
    exact (not_le_of_gt h) hz.2
  · have h : (0 : ℝ) < I.lo := by exact_mod_cast hpos
    exact (not_le_of_gt h) hz.1

/-- The caller must supply an enclosure for EVERY point of the pixel rectangle.
No continuity assumption is needed to exclude a zero of a total real function. -/
theorem empty_pixel_sound {X Y R : QInterval} {f : ℝ → ℝ → ℝ}
    (enclosure : ∀ x y, X.Contains x → Y.Contains y → R.Contains (f x y))
    (hc : classify R = .empty) :
    ¬ ∃ x y, X.Contains x ∧ Y.Contains y ∧ f x y = 0 := by
  rintro ⟨x, y, hx, hy, hzero⟩
  exact classify_empty_sound hc (enclosure x y hx hy) hzero

def pixelX : QInterval := ⟨1 / 2, 1, by norm_num⟩
def pixelY : QInterval := ⟨-(1 / 4), 1 / 4, by norm_num⟩

/-- The box [1/2, 1] × [-1/4, 1/4] maps into [1/4, 5/4] under x + y. -/
theorem example_bounds :
    (pixelX.add pixelY).lo = 1 / 4 ∧ (pixelX.add pixelY).hi = 5 / 4 := by
  norm_num [pixelX, pixelY, QInterval.add]

theorem example_classification : classify (pixelX.add pixelY) = .empty := by
  norm_num [classify, pixelX, pixelY, QInterval.add]

/-- Thus the box contains no point on the real line x + y = 0. -/
theorem example_empty_pixel :
    ¬ ∃ x y, pixelX.Contains x ∧ pixelY.Contains y ∧ x + y = 0 :=
  empty_pixel_sound (fun _ _ hx hy => add_encloses hx hy) example_classification

/-- Zero at an endpoint must remain unresolved by this classifier. -/
theorem zero_boundary_unknown : classify ⟨0, 1, by norm_num⟩ = .unknown := by
  norm_num [classify]

/-- Unknown is not evidence of a root: even the constant function 1 may be
enclosed by [-1, 1], which this classifier leaves unresolved. -/
theorem unknown_does_not_imply_root :
    classify ⟨-1, 1, by norm_num⟩ = .unknown ∧
    (∀ _x _y : ℝ, (QInterval.mk (-1) 1 (by norm_num)).Contains (1 : ℝ)) ∧
    ¬ ∃ _x _y : ℝ, (1 : ℝ) = 0 := by
  norm_num [classify, QInterval.Contains]

end GeneralizedIntervalArithmetic
