import SequenceRepresentations
import AuditPolicy
namespace GeneralizedIntervalArithmetic.SequenceRepresentationsChecks
open SequenceRepresentations Filter
open scoped Topology

def shrinking (n : ℕ) : ℚ := (1/2)^n

theorem shrinking_represents : Represents shrinking 0 := by
  simpa [Represents,shrinking] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1))

theorem same_value_distinct_streams :
    shrinking ≠ (fun _=>0) ∧ Represents shrinking 0 ∧ Represents (fun _=>0) 0 := by
  refine ⟨?_,shrinking_represents,by simpa using constant 0⟩
  intro h
  have hh := congrFun h 0
  norm_num [shrinking] at hh

theorem termwise_product : Represents (fun n=>shrinking n * shrinking n) 0 := by
  simpa using mul shrinking_represents shrinking_represents

/-- All denominators are nonzero, but the limit denominator is zero.
The two different numerator representatives of 0 yield different quotient limits. -/
theorem zero_limit_obstruction :
    (∀n, shrinking n ≠ 0) ∧
    Represents (fun n=>shrinking n / shrinking n) 1 ∧
    Represents (fun n=>0 / shrinking n) 0 ∧
    ¬ Represents (fun n=>shrinking n / shrinking n) 0 := by
  have hn : ∀n,shrinking n≠0 := fun n => pow_ne_zero n (by norm_num)
  have h1 : Represents (fun n=>shrinking n / shrinking n) 1 := by
    simpa [hn] using constant 1
  refine ⟨hn,h1,by simpa using constant 0,?_⟩
  intro h0
  have hh := unique h1 h0
  norm_num at hh

/-- Finite bad prefixes are permitted by convergence, not by pointwise division. -/
def earlyZero (n : ℕ) : ℚ := if n<3 then 0 else 1

theorem early_zero_represents : Represents earlyZero 1 := by
  change Tendsto (fun n=>(earlyZero n:ℝ)) atTop (𝓝 1)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  simp [earlyZero,not_lt.mpr hn]

theorem early_zero_division : earlyZero 0=0 ∧
    (∀ᶠ n in atTop,earlyZero n≠0) ∧
    Represents (fun n=>(1:ℚ)/earlyZero n) 1 := by
  have h := div (constant 1) early_zero_represents (by norm_num : (1:ℝ)≠0)
  exact ⟨by norm_num [earlyZero],h.1,by simpa using h.2⟩

/-- No common stopping index is supplied just by existence of a limit. -/
theorem arbitrary_finite_delay (N : ℕ) :
    Represents (fun n => if n≤N then (1:ℚ) else 0) 0 ∧
    (if N≤N then (1:ℚ) else 0) = 1 := by
  refine ⟨?_,by simp⟩
  unfold Represents
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop N] with n hn
  simp [not_le.mpr hn]

end GeneralizedIntervalArithmetic.SequenceRepresentationsChecks
#audit_namespace GeneralizedIntervalArithmetic.SequenceRepresentationsChecks
