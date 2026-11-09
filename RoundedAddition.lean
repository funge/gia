import Intervals

/-!
Conditional directed-rounding extension. The two local inequalities are
assumptions about the returned finite endpoints, NOT proofs of an FP operation.
No global rounding contract, FP encoding, or exceptional-value model is assumed.
The intended IEEE 754 directions are toward negative infinity for `down` and
toward positive infinity for `up`; only their enclosure consequence is used.
-/

namespace GeneralizedIntervalArithmetic

/-- Add intervals using candidate downward/upward rounding operations.
The caller supplies their enclosure contracts at the two exact endpoint sums.
Only these two calls need satisfy the contracts. -/
def roundedAdd (I J : QInterval) (down up : ℚ → ℚ)
    (hd : down (I.lo + J.lo) ≤ I.lo + J.lo)
    (hu : I.hi + J.hi ≤ up (I.hi + J.hi)) : QInterval :=
  ⟨down (I.lo + J.lo), up (I.hi + J.hi),
    hd.trans ((add_le_add I.ordered J.ordered).trans hu)⟩

/-- If the two rounding contracts hold, rounded addition encloses every real
sum. In particular, x and y need not themselves be representable FP values. -/
theorem rounded_add_encloses (I J : QInterval) (down up : ℚ → ℚ)
    (hd : down (I.lo + J.lo) ≤ I.lo + J.lo)
    (hu : I.hi + J.hi ≤ up (I.hi + J.hi))
    {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y) :
    (roundedAdd I J down up hd hu).Contains (x + y) := by
  have hexact := add_encloses hx hy
  constructor
  · have h : (down (I.lo + J.lo) : ℝ) ≤ ((I.lo + J.lo : ℚ) : ℝ) := by
      exact_mod_cast hd
    exact h.trans hexact.1
  · have h : ((I.hi + J.hi : ℚ) : ℝ) ≤ (up (I.hi + J.hi) : ℝ) := by
      exact_mod_cast hu
    exact hexact.2.trans h

/-- An empty classification remains sound after outward rounding, provided
the two local rounding contracts hold. -/
theorem rounded_add_empty_pixel (I J : QInterval) (down up : ℚ → ℚ)
    (hd : down (I.lo + J.lo) ≤ I.lo + J.lo)
    (hu : I.hi + J.hi ≤ up (I.hi + J.hi))
    (hc : classify (roundedAdd I J down up hd hu) = .empty) :
    ¬ ∃ x y, I.Contains x ∧ J.Contains y ∧ x + y = 0 :=
  empty_pixel_sound
    (fun _ _ hx hy => rounded_add_encloses I J down up hd hu hx hy) hc

/-- Concrete candidate endpoints around 1 + 2^-53. These are exact rational
inequalities, not a claim that an implementation returns these candidates. -/
theorem halfway_candidate_bounds :
    (1 : ℚ) < 1 + 1 / 2 ^ 53 ∧
    (1 : ℚ) + 1 / 2 ^ 53 < 1 + 1 / 2 ^ 52 := by
  norm_num

end GeneralizedIntervalArithmetic
