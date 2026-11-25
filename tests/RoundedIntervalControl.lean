import RoundedIntervalControl
import AuditPolicy
namespace GeneralizedIntervalArithmetic.RoundedIntervalControlChecks
open RoundedIntervalControl
example := staged
/-- Both staged enclosures still contain the real scalar answer. -/
theorem real_answer :
    (interval 200 220 (by norm_num)).Contains 202 ∧
    (interval 200 210 (by norm_num)).Contains 202 := by
  norm_num [interval,QInterval.Contains]
end GeneralizedIntervalArithmetic.RoundedIntervalControlChecks
#audit_namespace GeneralizedIntervalArithmetic.RoundedIntervalControlChecks
