import IntervalAlgebra
import AuditPolicy
namespace GeneralizedIntervalArithmetic.IntervalAlgebraChecks
open IntervalAlgebra

def symmetric : QInterval := ⟨-1,1,by norm_num⟩
theorem strict_subdistributivity :
    ((symmetric.mul (.point 1)).add (symmetric.mul (.point (-1)))).Contains 1 ∧
    ¬ (symmetric.mul ((QInterval.point 1).add (.point (-1)))).Contains 1 := by
  norm_num [symmetric,QInterval.point,QInterval.add,QInterval.mul,QInterval.Contains]

theorem zero_singleton_control :
    ∀ z : ℝ, ((QInterval.point 0).mul (symmetric.add symmetric)).Contains z ↔ z=0 := by
  intro z
  norm_num [symmetric,QInterval.point,QInterval.add,QInterval.mul,QInterval.Contains]
  exact ⟨fun h => le_antisymm h.2 h.1,fun h => by simp [h]⟩

theorem right_endpoint_trail :
    (symmetric.add (symmetric.add symmetric)).Contains ((1+1)+1) :=
  addition_trail (by norm_num [symmetric,QInterval.Contains])
    (by norm_num [symmetric,QInterval.Contains]) (by norm_num [symmetric,QInterval.Contains])
end GeneralizedIntervalArithmetic.IntervalAlgebraChecks
#audit_namespace GeneralizedIntervalArithmetic.IntervalAlgebraChecks
