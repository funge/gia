import AffineConjunction

namespace GeneralizedIntervalArithmetic.AffineDemotionLimits

/-- A real affine minorant of square on the entire closed parameter domain. -/
def Minorant (m c : ℝ) : Prop := ∀ t ∈ Set.Icc (0:ℝ) 1, m*t+c ≤ t^2

theorem zero_minorant : Minorant 0 0 := by
  intro t _; nlinarith [sq_nonneg t]

theorem endpoint_tangent_minorant : Minorant 2 (-1) := by
  intro t _; nlinarith [sq_nonneg (t-1)]

/-- No affine minorant dominates even these two sound affine candidates. -/
theorem incompatible_minorants (m c : ℝ) (h : Minorant m c)
    (hzero : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ m*t+c)
    (hone : ∀ t ∈ Set.Icc (0:ℝ) 1, 2*t-1 ≤ m*t+c) : False := by
  have h0 := h 0 (by constructor <;> norm_num)
  have h1 := h 1 (by constructor <;> norm_num)
  have hh := h (1/2) (by constructor <;> norm_num)
  have z0 := hzero 0 (by constructor <;> norm_num)
  have o1 := hone 1 (by constructor <;> norm_num)
  norm_num at h0 h1 hh z0 o1
  linarith

/-- Tupper §2.9.3: pointwise greatest affine demotion need not exist.
This is an existential obstruction, not a claim that every input lacks a best bound. -/
theorem no_greatest_minorant :
    ¬ ∃ m c : ℝ, Minorant m c ∧
      ∀ n d : ℝ, Minorant n d → ∀ t ∈ Set.Icc (0:ℝ) 1, n*t+d ≤ m*t+c := by
  rintro ⟨m,c,h,hmax⟩
  apply incompatible_minorants m c h
  · simpa using hmax 0 0 zero_minorant
  · simpa [sub_eq_add_neg] using hmax 2 (-1) endpoint_tangent_minorant

/-- The dual obstruction for affine majorants of negative square. -/
theorem no_least_majorant :
    ¬ ∃ m c : ℝ, (∀ t ∈ Set.Icc (0:ℝ) 1, -(t^2) ≤ m*t+c) ∧
      ∀ n d : ℝ, (∀ t ∈ Set.Icc (0:ℝ) 1, -(t^2) ≤ n*t+d) →
        ∀ t ∈ Set.Icc (0:ℝ) 1, m*t+c ≤ n*t+d := by
  rintro ⟨m,c,h,hmin⟩
  apply no_greatest_minorant
  refine ⟨-m,-c,?_,?_⟩
  · intro t ht; have := h t ht; nlinarith
  · intro n d hn t ht
    have hg : ∀ s ∈ Set.Icc (0:ℝ) 1, -(s^2) ≤ (-n)*s+(-d) := by
      intro s hs; have := hn s hs; nlinarith
    have := hmin (-n) (-d) hg t ht
    nlinarith

end GeneralizedIntervalArithmetic.AffineDemotionLimits
