import SineTaylor

namespace GeneralizedIntervalArithmetic.CosineTaylor

noncomputable def polynomial (x : ℝ) : ℝ := 1 - x^2/2 + x^4/24 - x^6/720

theorem bounds_nonnegative {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    polynomial x ≤ Real.cos x ∧ Real.cos x ≤ polynomial x + x^8/40320 := by
  have ha : Antitone (fun n : ℕ => x^(2*n) / (Nat.factorial (2*n) : ℝ)) := by
    intro m n hmn
    apply div_le_div₀ (by positivity)
    · exact pow_le_pow_of_le_one hx h1 (by omega)
    · positivity
    · exact_mod_cast Nat.factorial_le (show 2*m ≤ 2*n by omega)
  have hs := (Real.hasSum_cos x).tendsto_sum_nat
  simp_rw [mul_div_assoc] at hs
  have hl := Antitone.alternating_series_le_tendsto hs ha 2
  have hu := Antitone.tendsto_le_alternating_series hs ha 2
  norm_num [Finset.sum_range_succ, Nat.factorial, polynomial] at hl hu ⊢
  constructor <;> linarith

theorem polynomial_even (x : ℝ) : polynomial (-x) = polynomial x := by
  unfold polynomial
  ring

/-- Even symmetry extends the sixth-degree bracket across zero. -/
theorem bounds {x : ℝ} (hx : -1 ≤ x) (h1 : x ≤ 1) :
    polynomial x ≤ Real.cos x ∧ Real.cos x ≤ polynomial x + x^8/40320 := by
  by_cases h : 0 ≤ x
  · exact bounds_nonnegative h h1
  · have hh := bounds_nonnegative (x := -x) (by linarith) (by linarith)
    have h8 : (-x)^8 = x^8 := by ring
    rw [polynomial_even, Real.cos_neg, h8] at hh
    exact hh

theorem remainder_width {x : ℝ} (hx : -1 ≤ x) (h1 : x ≤ 1) :
    0 ≤ x^8/40320 ∧ x^8/40320 ≤ 1/40320 := by
  have hsq : 0 ≤ x^2 := sq_nonneg x
  have hsq1 : x^2 ≤ 1 := by nlinarith
  have hp := pow_le_pow_left₀ hsq hsq1 4
  constructor
  · positivity
  · norm_num at hp
    nlinarith [show (x^2)^4 = x^8 by ring]

theorem maximum_at_zero (x : ℝ) : Real.cos x ≤ Real.cos 0 := by
  simpa using Real.cos_le_one x

end GeneralizedIntervalArithmetic.CosineTaylor
