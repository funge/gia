import Intervals

namespace GeneralizedIntervalArithmetic

private theorem mul_between {a b x : ℝ} (hx : a ≤ x ∧ x ≤ b) (y : ℝ) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hy),
      (mul_le_mul_of_nonneg_right hx.2 hy).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hy),
      (mul_le_mul_of_nonpos_right hx.1 hy).trans (le_max_left _ _)⟩

/-- Real four-corner enclosure, reusable independently of rational endpoint storage. -/
theorem four_products {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
    x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have ha := mul_between hy a
  have hb := mul_between hy b
  simp only [mul_comm] at ha hb
  have hxy := mul_between hx y
  exact ⟨(min_le_min ha.1 hb.1).trans hxy.1,
    hxy.2.trans (max_le_max ha.2 hb.2)⟩

def QInterval.point (q : ℚ) : QInterval := ⟨q, q, le_rfl⟩

/-- Exact four-corner product bounds; repeated-variable dependencies are lost. -/
def QInterval.mul (I J : QInterval) : QInterval :=
  ⟨min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi)),
   max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi)),
   ((min_le_left _ _).trans (min_le_left _ _)).trans
     ((le_max_left _ _).trans (le_max_left _ _))⟩

theorem mul_encloses {I J : QInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.mul J).Contains (x*y) := by
  simpa [QInterval.Contains, QInterval.mul] using four_products hx hy

def QInterval.AwayZero (I : QInterval) : Prop := I.hi < 0 ∨ 0 < I.lo

instance (I : QInterval) : Decidable I.AwayZero :=
  inferInstanceAs (Decidable (I.hi < 0 ∨ 0 < I.lo))

def QInterval.recip (I : QInterval) (h : I.AwayZero) : QInterval :=
  ⟨I.hi⁻¹, I.lo⁻¹, by
    rcases h with hn | hp
    · exact (inv_le_inv_of_neg hn (I.ordered.trans_lt hn)).2 I.ordered
    · exact inv_anti₀ hp I.ordered⟩

theorem awayZero_nonzero {I : QInterval} {x : ℝ}
    (h : I.AwayZero) (hx : I.Contains x) : x ≠ 0 := by
  apply classify_empty_sound (I := I) _ hx
  change I.hi < 0 ∨ 0 < I.lo at h
  simp [classify, h]

theorem recip_encloses {I : QInterval} {x : ℝ}
    (h : I.AwayZero) (hx : I.Contains x) : (I.recip h).Contains x⁻¹ := by
  change ((I.hi⁻¹ : ℚ) : ℝ) ≤ x⁻¹ ∧ x⁻¹ ≤ ((I.lo⁻¹ : ℚ) : ℝ)
  simp only [Rat.cast_inv]
  rcases h with hn | hp
  · have hn' : (I.hi : ℝ) < 0 := by exact_mod_cast hn
    have hx' := hx.2.trans_lt hn'
    exact ⟨(inv_le_inv_of_neg hn' hx').2 hx.2,
      (inv_le_inv_of_neg hx' (hx.1.trans_lt hx')).2 hx.1⟩
  · have hp' : (0 : ℝ) < I.lo := by exact_mod_cast hp
    exact ⟨inv_anti₀ (hp'.trans_le hx.1) hx.2, inv_anti₀ hp' hx.1⟩

end GeneralizedIntervalArithmetic
