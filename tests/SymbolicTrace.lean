import SymbolicTrace
import AuditPolicy
namespace GeneralizedIntervalArithmetic.SymbolicTraceChecks
open SymbolicTrace

theorem lower_endpoint : trace 0 = {0} := by
  rw [trace_exact (by norm_num)]; norm_num [value]

theorem upper_endpoint : trace 1 = {Real.sin 1+1/(1+Real.pi)} := by
  rw [trace_exact (by norm_num)]; norm_num [value]

theorem interior : trace (1/2) = {value (1/2)} := trace_exact (by norm_num)

theorem negative_root : trace (-1) = ∅ := negative_absent (by norm_num)

theorem quotient_zero_guard : quot {1} {0} = ∅ := by
  ext z; simp [quot_singletons]

/-- The total real expression still denotes a number at -1. That payload does
not create a value of the original partial expression. -/
theorem payload_not_defined : bounds.Contains (-1) (value (-1)) ∧
    ¬(trace (-1)).Nonempty := by
  exact ⟨(bounds_exact _ _).mpr rfl,by rw [defined_iff]; norm_num⟩

theorem external_hole :
    ¬(model {p : ℝ | p≠1/2}).domain.possible (1/2) ∧
    (trace (1/2)).Nonempty := by
  constructor
  · simp [model]
  · rw [defined_iff]; norm_num

/-- Equal bounds at each parameter do not mean a constant projected range. -/
theorem projection_not_singleton_zero :
    {z | ∃ p ∈ Set.Icc (0:ℝ) 1, z∈trace p} ≠ {0} := by
  have hs : 0<Real.sin 1 := Real.sin_pos_of_pos_of_lt_pi (by norm_num)
    (by linarith [Real.two_le_pi])
  have hv : 0<value 1 := by
    dsimp [value]; norm_num
    exact add_pos hs (by positivity)
  intro h
  have hm : value 1 ∈ ({z | ∃ p ∈ Set.Icc (0:ℝ) 1, z∈trace p}:Set ℝ) :=
    ⟨1,by norm_num,(trace_iff _ _).mpr ⟨by norm_num,rfl⟩⟩
  rw [h] at hm
  exact (ne_of_gt hv) hm

end GeneralizedIntervalArithmetic.SymbolicTraceChecks
#audit_namespace GeneralizedIntervalArithmetic.SymbolicTraceChecks
