import LinearEvaluator
import AuditPolicy

namespace GeneralizedIntervalArithmetic.ConstantEmbeddingChecks

def X : QInterval := ⟨-2,3,by norm_num⟩
def Y : QInterval := ⟨-1,4,by norm_num⟩
def polynomial : Expr := .mul (.add .x .y) (.sub .x .y)
def output := X.add Y |>.mul (X.sub Y)

theorem pointwise_embedding (t z : ℝ) :
    (LinearInterval.constant X).Contains t z ↔ X.Contains z :=
  linear_constant_contains X t z

theorem source_zero_slopes :
    ((LinearInterval.constant X).lower.coefficients,
      (LinearInterval.constant X).upper.coefficients) = ((-2,0),(3,0)) := by
  decide +kernel

theorem distinct_intervals : LinearInterval.constant X ≠ LinearInterval.constant Y := by
  intro h
  have he := linear_constant_injective h
  have hlo := congrArg QInterval.lo he
  norm_num [X,Y] at hlo

theorem composed_evaluation :
    evalLinear (.constant X) (.constant Y) polynomial = some (.constant output) := by
  simp [polynomial,evalLinear,combineLinear,linear_constant_add,
    linear_constant_sub,linear_constant_mul,output]

theorem ordinary_correspondence :
    ∃ I, eval exactBackend X Y polynomial = some I ∧
      LinearInterval.constant output = .constant I :=
  evalLinear_constant_correspondence X Y composed_evaluation

theorem computed_bounds : (output.lo,output.hi) = (-42,28) := by
  norm_num [output,X,Y,QInterval.add,QInterval.sub,QInterval.mul]

theorem ordinary_computed :
    (eval exactBackend X Y polynomial).map (fun I => (I.lo,I.hi)) = some (-42,28) := by
  norm_num [eval,polynomial,combine,exactBackend,X,Y,QInterval.add,QInterval.sub,QInterval.mul]

theorem actual_value : Value 2 1 polynomial 3 := by
  have hx : Value (2:ℝ) 1 .x 2 := Value.x
  have hy : Value (2:ℝ) 1 .y 1 := Value.y
  have h := Value.mul (Value.add hx hy) (Value.sub hx hy)
  norm_num at h
  exact h

theorem actual_enclosure : (LinearInterval.constant output).Contains (1/2) 3 := by
  apply evalLinear_sound (by norm_num) _ _ actual_value composed_evaluation
  · rw [linear_constant_contains]
    norm_num [X,QInterval.Contains]
  · rw [linear_constant_contains]
    norm_num [Y,QInterval.Contains]

/-- Constant embedding does not restore dependence lost by ordinary intervals. -/
theorem constant_cancellation_wide :
    (((LinearInterval.constant X).sub (.constant X)).hull.lo,
      ((LinearInterval.constant X).sub (.constant X)).hull.hi) = (-5,5) := by
  decide +kernel

/-- The left inverse hull is not asserted to commute with multiplication on
arbitrary linear intervals. The current curvature bound makes this concrete. -/
def parameter : LinearInterval := .exact (QAffine.ofCoefficients 0 1)

theorem hull_multiplication_control :
    ((parameter.mul parameter).hull.lo,(parameter.mul parameter).hull.hi) = (-1/4,1) ∧
    ((parameter.hull.mul parameter.hull).lo,(parameter.hull.mul parameter.hull).hi) = (0,1) := by
  decide +kernel

/-- The success-conditioned interpreter bridge has no unrestricted converse. -/
theorem unsupported_division_control :
    (evalLinear (.constant X) (.constant Y) (.div (.const 1) (.const 1))).isSome = false ∧
    (eval exactBackend X Y (.div (.const 1) (.const 1))).isSome = true := by
  decide +kernel

end GeneralizedIntervalArithmetic.ConstantEmbeddingChecks
#audit_namespace GeneralizedIntervalArithmetic.ConstantEmbeddingChecks
