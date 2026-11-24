import CoefficientWitnesses
import AuditPolicy
namespace GeneralizedIntervalArithmetic.CoefficientWitnessesChecks
open CoefficientWitnesses

def unit : QInterval := ⟨0,1,by norm_num⟩
def zero : QInterval := ⟨0,0,by norm_num⟩

theorem independent_choices (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    t ∈ marginal (intervalPairs unit zero) t := by
  exact ⟨(t,0),⟨by simpa [unit,QInterval.Contains] using ht,by simp [zero,QInterval.Contains]⟩,by simp⟩

/-- Every pointwise ordinary/affine bound admits this curve, but no fixed
constant coefficient in [0,1] produces the whole curve. -/
theorem all_bounds (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (IntervalCoefficientVariants.form unit zero).Contains t t := by
  apply (IntervalCoefficientVariants.exact_form unit zero ht.1 t).mp
  exact independent_choices t ht

theorem not_one_witness : ¬ realizes (intervalPairs unit zero) (Set.Icc 0 1) (fun t => t) := by
  rw [realizes_iff _ _ _ (by norm_num) (by norm_num)]
  norm_num [intervalPairs,unit,zero,QInterval.Contains]

def useTimes : Bool → ℝ := fun b => if b then 1 else 0
def useValues : Bool → ℝ := fun b => if b then 1 else 0

theorem repeated_marginals : ∀ b, useValues b ∈ marginal (intervalPairs unit zero) (useTimes b) := by
  intro b; cases b <;> exact independent_choices _ (by norm_num [useTimes,useValues])

theorem repeated_not_joint : useValues ∉ samples (intervalPairs unit zero) useTimes := by
  rintro ⟨⟨p,q⟩,⟨_,hq⟩,hv⟩
  have hq0 : q=0 := by
    norm_num [zero,QInterval.Contains] at hq
    exact le_antisymm hq.2 hq.1
  have h0 := hv false
  have h1 := hv true
  simp [useTimes,useValues,hq0] at h0 h1
  linarith

theorem mixed_exact : coded (fun p : ℤ => (p:ℝ)) (fun q : ℚ => (q:ℝ))
    Set.univ (Set.Icc 0 1) (fun t => 2+(3/2)*t) := by
  refine ⟨(2,3/2),Set.mem_univ _,?_⟩
  intro t _; norm_num

theorem fractional_intercept_rejected : ¬ coded (fun p : ℤ => (p:ℝ)) (fun q : ℚ => (q:ℝ))
    Set.univ (Set.Icc 0 1) (fun _ => 1/2) := by
  rw [integer_rational_iff _ _ (by norm_num) (by norm_num)]
  rintro ⟨⟨p,hp⟩,_,_⟩
  have h0 : (0:ℤ) < p := by exact_mod_cast (show (0:ℝ)<p by linarith)
  have h1 : p < (1:ℤ) := by exact_mod_cast (show (p:ℝ)<1 by linarith)
  omega

/-- A one-use domain cannot justify recovery from two absent anchor uses. -/
theorem singleton_domain : realizes (intervalPairs unit zero) {(1/2:ℝ)} (fun t => t^2) := by
  refine ⟨(1/4,0),?_,?_⟩
  · norm_num [intervalPairs,unit,zero,QInterval.Contains]
  · intro t ht; simp only [Set.mem_singleton_iff] at ht; subst t; norm_num

theorem empty_stays_ineligible (f : ℝ → ℝ) : ¬ realizes ∅ ∅ f := no_coefficients ∅ f

theorem empty_parameter_control (f : ℝ → ℝ) : realizes (intervalPairs unit zero) ∅ f := by
  rw [empty_parameters]
  exact ⟨(0,0),by norm_num [intervalPairs,unit,zero,QInterval.Contains]⟩

/-- A constrained pair is not decoded as the product of its marginals. -/
theorem constrained_pair_decode :
    decodePairs (fun p : ℤ => (p:ℝ)) (fun q : ℚ => (q:ℝ)) {(0,1),(1,0)} =
      ({((0:ℝ),1),(1,0)} : Set (ℝ × ℝ)) := by
  ext c
  simp [decodePairs,eq_comm]

theorem not_independent_pair : ((1:ℝ),1) ∉
    decodePairs (fun p : ℤ => (p:ℝ)) (fun q : ℚ => (q:ℝ)) {(0,1),(1,0)} := by
  rw [constrained_pair_decode]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Prod.mk.injEq]
  norm_num

end GeneralizedIntervalArithmetic.CoefficientWitnessesChecks
#audit_namespace GeneralizedIntervalArithmetic.CoefficientWitnessesChecks
