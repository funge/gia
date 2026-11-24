import HyperrealInfinitesimal
import AuditPolicy

namespace GeneralizedIntervalArithmetic.HyperrealInfinitesimalChecks

theorem positive_smaller_than_half :
    0 < Hyperreal.epsilon ∧ Hyperreal.epsilon < Hyperreal.ofReal (1/2) :=
  ⟨Hyperreal.epsilon_pos,Hyperreal.epsilon_lt_pos _ (by norm_num)⟩

theorem not_real_zero : Hyperreal.epsilon ≠ Hyperreal.ofReal 0 := by
  intro h
  exact HyperrealInfinitesimal.epsilon_not_real ⟨0,h.symm⟩

end GeneralizedIntervalArithmetic.HyperrealInfinitesimalChecks
#audit_namespace GeneralizedIntervalArithmetic.HyperrealInfinitesimalChecks
