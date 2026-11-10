import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring

/-!
Restricted counterpart of Tupper §3.1.6, printed pp.48–49: fifth-degree sine
polynomial and a seventh-order remainder. See HARDWARE_SINE.md for the source
comparison. These are real-analysis proofs, independent of the native adapter.
-/
namespace GeneralizedIntervalArithmetic.SineTaylor

noncomputable def polynomial (x : ℝ) : ℝ := x - x^3 / 6 + x^5 / 120

/-- Alternating partial sums bracket sine throughout [0, 1]. -/
theorem bounds {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    polynomial x - x^7 / 5040 ≤ Real.sin x ∧ Real.sin x ≤ polynomial x := by
  have ha : Antitone (fun n : ℕ => x^(2*n+1) / (Nat.factorial (2*n+1) : ℝ)) := by
    intro m n hmn
    apply div_le_div₀ (by positivity)
    · exact pow_le_pow_of_le_one hx h1 (by omega)
    · positivity
    · exact_mod_cast Nat.factorial_le (show 2*m+1 ≤ 2*n+1 by omega)
  have hs := (Real.hasSum_sin x).tendsto_sum_nat
  simp_rw [mul_div_assoc] at hs
  have hl := Antitone.alternating_series_le_tendsto hs ha 2
  have hu := Antitone.tendsto_le_alternating_series hs ha 1
  norm_num [Finset.sum_range_succ, Nat.factorial, polynomial] at hl hu ⊢
  constructor <;> linarith

/-- Analytic point-width budget only; not a hardware rounding-error bound. -/
theorem remainder_width {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ x^7 / 5040 ∧ x^7 / 5040 ≤ 1/5040 := by
  constructor
  · positivity
  · have hp : x^7 ≤ (1 : ℝ)^7 := pow_le_pow_left₀ hx h1 7
    norm_num at hp
    linarith

end GeneralizedIntervalArithmetic.SineTaylor
