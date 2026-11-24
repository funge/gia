import ExceptionalFamilies
import AuditPolicy
namespace GeneralizedIntervalArithmetic.ExceptionalFamiliesChecks
open ExceptionalFamilies

theorem finite_shared_not_lambda :
    differenceScaled (.finite 8) (.finite 8) (1/2) = some (.finite 4) ∧
    differenceScaled .posInf .posInf (1/2) = some .undefined := by
  constructor
  · norm_num [differenceScaled]
  · exact source_midpoint

theorem negative_independent_not_shared : (-1:ℝ) ∈ independentImage ∧
    (-1:ℝ) ∉ sharedImage := by rw [independent_exact,shared_exact]; norm_num

theorem zero_shared_witness : (0:ℝ) ∈ sharedImage := ⟨0,le_rfl,by ring⟩

theorem no_value_in_literal_result (x : ℝ) :
    x ∉ realOutputs (differenceScaled .posInf .posInf (1/2)) := by
  rw [literal_midpoint_no_real]; simp

theorem unbounded_bounds_keep_values (x : ℝ) :
    x ∈ ExtendedImageHull.interval ⊥ ⊤ ∧
    x ∉ ExtendedImageHull.interval ⊤ ⊤ := by
  rw [bound_semantics.1,bound_semantics.2.2]; simp

theorem zero_endpoint_not_extrapolated :
    differenceScaled .posInf .posInf 0 = none ∧
    differenceScaled .posInf .posInf 1 = none := by
  constructor <;> apply other_parameters_unmodeled <;> norm_num

theorem empty_projection_not_undefined :
    realOutputs none = realOutputs (some .undefined) ∧
    (none : Option ExceptionalComparisons.Value) ≠ some .undefined := by
  exact ⟨rfl,by simp⟩

theorem bound_order_not_source_comparison : (⊤:EReal)≤⊤ ∧
    ExceptionalComparisons.observe .le .posInf .posInf = some false := ⟨le_rfl,rfl⟩

end GeneralizedIntervalArithmetic.ExceptionalFamiliesChecks
#audit_namespace GeneralizedIntervalArithmetic.ExceptionalFamiliesChecks
