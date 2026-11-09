import EvaluatorRounding
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Ring

namespace GeneralizedIntervalArithmetic

noncomputable def segment (a b t : ℝ) : ℝ := (1-t)*a + t*b

@[simp] theorem segment_zero (a b : ℝ) : segment a b 0 = a := by simp [segment]
@[simp] theorem segment_one (a b : ℝ) : segment a b 1 = b := by simp [segment]

theorem segment_continuous (a b : ℝ) : Continuous (segment a b) :=
  ((continuous_const.sub continuous_id).mul continuous_const).add
    (continuous_id.mul continuous_const)

theorem segment_mem {I : QInterval} {a b t : ℝ}
    (ha : I.Contains a) (hb : I.Contains b) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    I.Contains (segment a b t) := by
  have h1 : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  constructor
  · calc
      (I.lo : ℝ) = (1-t)*(I.lo : ℝ) + t*(I.lo : ℝ) := by ring
      _ ≤ segment a b t := add_le_add
        (mul_le_mul_of_nonneg_left ha.1 h1) (mul_le_mul_of_nonneg_left hb.1 ht.1)
  · calc
      segment a b t ≤ (1-t)*(I.hi : ℝ) + t*(I.hi : ℝ) := add_le_add
        (mul_le_mul_of_nonneg_left ha.2 h1) (mul_le_mul_of_nonneg_left hb.2 ht.1)
      _ = (I.hi : ℝ) := by ring

/-- A certified nonpositive/ nonnegative pair of endpoint enclosures plus
continuity implies a zero. Equality is allowed, so endpoint roots are retained. -/
theorem certified_curve_zero {g : ℝ → ℝ} {L U : QInterval}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hL : L.Contains (g 0)) (hU : U.Contains (g 1))
    (hn : L.hi ≤ 0) (hp : 0 ≤ U.lo) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, g t = 0 := by
  have hn' : (L.hi : ℝ) ≤ 0 := by exact_mod_cast hn
  have hp' : (0 : ℝ) ≤ U.lo := by exact_mod_cast hp
  exact intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hg
    ⟨hL.2.trans hn', hp'.trans hU.1⟩

/-- Presence requires a continuous, defined witness along the entire segment.
Endpoint signs alone do not justify presence for a partial expression. -/
theorem segment_presence {e : Expr} {X Y L U : QInterval}
    {ax ay bx by_ : ℝ} {g : ℝ → ℝ}
    (hax : X.Contains ax) (hay : Y.Contains ay)
    (hbx : X.Contains bx) (hby : Y.Contains by_)
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Value (segment ax bx t) (segment ay by_ t) e (g t))
    (hL : L.Contains (g 0)) (hU : U.Contains (g 1))
    (hn : L.hi ≤ 0) (hp : 0 ≤ U.lo) :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y e 0 := by
  obtain ⟨t, ht, hz⟩ := certified_curve_zero hg hL hU hn hp
  exact ⟨_, _, segment_mem hax hbx ht, segment_mem hay hby ht, hz ▸ hv t ht⟩

end GeneralizedIntervalArithmetic
