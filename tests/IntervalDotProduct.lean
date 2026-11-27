import IntervalDotProduct
import AuditPolicy
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace GeneralizedIntervalArithmetic.IntervalDotProductChecks
open IntervalDotProduct
open scoped BigOperators

def inputs : Fin 2 → QInterval := ![⟨-1,2,by norm_num⟩,⟨3,4,by norm_num⟩]
def factors : Fin 2 → QInterval := ![⟨-2,1,by norm_num⟩,⟨-1,2,by norm_num⟩]

theorem mixed_bounds : (bounds inputs factors).lo = -8 ∧ (bounds inputs factors).hi = 10 := by
  simp only [bounds,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  norm_num [inputs,factors,QInterval.mul]

theorem mixed_lower_witness :
    InBox inputs ![2,4] ∧ InBox factors ![-2,-1] ∧ dot ![2,4] ![-2,-1] = -8 := by
  constructor
  · intro i; fin_cases i <;> norm_num [inputs,QInterval.Contains]
  constructor
  · intro i; fin_cases i <;> norm_num [factors,QInterval.Contains]
  · norm_num [dot,Fin.sum_univ_succ]

theorem mixed_upper_witness :
    InBox inputs ![2,4] ∧ InBox factors ![1,2] ∧ dot ![2,4] ![1,2] = 10 := by
  constructor
  · intro i; fin_cases i <;> norm_num [inputs,QInterval.Contains]
  constructor
  · intro i; fin_cases i <;> norm_num [factors,QInterval.Contains]
  · norm_num [dot,Fin.sum_univ_succ]

/-- The actual public reference entry point, including negative and zero weights. -/
def weights : Fin 3 → ℚ := ![-2,3,0]
def features : Fin 3 → QInterval :=
  ![⟨-1,2,by norm_num⟩,⟨1,4,by norm_num⟩,⟨-100,100,by norm_num⟩]

theorem fixed_weights_bounds :
    (weightedBounds weights features).lo = -1 ∧ (weightedBounds weights features).hi = 14 := by
  norm_num [weightedBounds,bounds,weights,features,QInterval.mul,QInterval.point,Fin.sum_univ_succ]

theorem fixed_weights_enclose (x : Fin 3 → ℝ) (hx : InBox features x) :
    -1 ≤ dot (fun i => (weights i : ℝ)) x ∧ dot (fun i => (weights i : ℝ)) x ≤ 14 := by
  have h := weighted_sound weights hx
  simpa only [QInterval.Contains,fixed_weights_bounds.1,fixed_weights_bounds.2,
    Rat.cast_neg,Rat.cast_one,Rat.cast_ofNat] using h

theorem empty_dimension (I J : Fin 0 → QInterval) (x y : Fin 0 → ℝ) :
    (bounds I J).lo = 0 ∧ (bounds I J).hi = 0 ∧ dot x y = 0 := by
  simp [bounds,dot]

theorem singleton_inputs :
    (bounds (fun _ : Fin 1 => QInterval.point (3/2))
      (fun _ => QInterval.point (-2))).lo = -3 ∧
    (bounds (fun _ : Fin 1 => QInterval.point (3/2))
      (fun _ => QInterval.point (-2))).hi = -3 := by
  norm_num [bounds,QInterval.mul,QInterval.point,Fin.sum_univ_succ]

def unitBox : Fin 1 → QInterval := fun _ => ⟨-1,1,by norm_num⟩

/-- Independence is essential to attainment: the relaxed bound admits -1,
but reusing the same vector cannot attain any negative value. -/
theorem self_dependency : (bounds unitBox unitBox).Contains (-1) ∧
    ¬∃ x : Fin 1 → ℝ, InBox unitBox x ∧ dot x x = -1 := by
  constructor
  · norm_num [bounds,unitBox,QInterval.mul,QInterval.Contains,Fin.sum_univ_succ]
  · rintro ⟨x,_,he⟩
    have hn : 0 ≤ dot x x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
    linarith

/-- Shared coordinates can also make fixed-weight interval bounds non-tight. -/
theorem shared_feature_cancellation :
    (weightedBounds (![1,-1] : Fin 2 → ℚ)
      (fun _ => (⟨-1,1,by norm_num⟩ : QInterval))).lo = -2 ∧
    (∀ t : ℝ, dot ![1,-1] ![t,t] = 0) := by
  constructor
  · norm_num [weightedBounds,bounds,QInterval.mul,QInterval.point,Fin.sum_univ_succ]
  · intro t; simp [dot,Fin.sum_univ_succ]

#eval ((bounds inputs factors).lo, (bounds inputs factors).hi)
#eval ((weightedBounds weights features).lo, (weightedBounds weights features).hi)

end GeneralizedIntervalArithmetic.IntervalDotProductChecks
#audit_namespace GeneralizedIntervalArithmetic.IntervalDotProductChecks
