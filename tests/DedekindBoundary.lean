import DedekindBoundary
import AuditPolicy
namespace GeneralizedIntervalArithmetic.DedekindBoundaryChecks
open DedekindBoundary

theorem distinct_same_real : strict 1 ≠ closed 1 ∧
    sSup (values (strict 1)) = 1 ∧ sSup (values (closed 1)) = 1 :=
  ⟨by simpa using distinct_rational_boundary 1 (by norm_num),same_supremum (by norm_num)⟩

theorem zero_totalization_is_not_lub :
    sSup (values (strict 0)) = 0 ∧ ¬ ∃r:ℝ,IsLUB (values (strict 0)) r := by
  refine ⟨?_,empty_no_real_lub⟩
  simp [zero_boundary.1,values]

theorem downward_is_a_real_obligation :
    ¬ (∀ c∈({1}:Set ℚ), ∀ q:ℚ, 0≤q → q<c → q∈({1}:Set ℚ)) := by
  intro h
  have hh := h 1 (by simp) (1/2) (by norm_num) (by norm_num)
  norm_num at hh

theorem improper_cut_unbounded : ¬ BddAbove (values {q:ℚ|0≤q}) := by
  rintro ⟨b,hb⟩
  obtain ⟨q,hq⟩ := exists_rat_gt (max b 0)
  have h0 : 0≤q := by exact_mod_cast (le_max_right b 0).trans hq.le
  have h1 := hb (show (q:ℝ)∈values {q:ℚ|0≤q} from ⟨q,h0,rfl⟩)
  exact (not_le_of_gt ((le_max_left b 0).trans_lt hq)) h1

end GeneralizedIntervalArithmetic.DedekindBoundaryChecks
#audit_namespace GeneralizedIntervalArithmetic.DedekindBoundaryChecks
