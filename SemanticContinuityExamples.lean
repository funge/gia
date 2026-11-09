import SemanticContinuity

namespace GeneralizedIntervalArithmetic.SemanticContinuityExamples

def X : LinearInterval := .exact ⟨0,1⟩
def Y : LinearInterval := .exact ⟨0,0⟩
def dependentQuotient : Expr :=
  .div (.sub .x (.const (1/2))) (.add (.sub .x .x) (.const 1))

theorem ordinary_unknown :
    (eval exactBackend ⟨0,1,by norm_num⟩ (.point 0) dependentQuotient).isNone = true := by
  decide +kernel

theorem linear_success : (evalGuarded X Y dependentQuotient).isSome := by decide +kernel

def result : LinearInterval := (evalGuarded X Y dependentQuotient).get linear_success

private theorem hx (t : ℝ) : X.Contains t t := by
  apply (linear_exact_contains _ _ _).mpr
  simp [QAffine.value]
private theorem hy (t : ℝ) : Y.Contains t 0 := by
  apply (linear_exact_contains _ _ _).mpr
  simp [QAffine.value]

theorem dependent_curve_certificate :
    ContinuousOn (fun t => dependentQuotient.realValue t 0) (Set.Icc (0:ℝ) 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, Value t 0 dependentQuotient (dependentQuotient.realValue t 0) :=
  evalGuarded_continuousOn (fun _ h => h) continuousOn_id continuousOn_const
    (fun t _ => hx t) (fun t _ => hy t) (Option.some_get linear_success).symm

/-- Existing IVT machinery consumes the new certificate and produces an actual
partial-semantic root, despite the ordinary interval guard being inconclusive. -/
theorem dependent_defined_root : ∃ t ∈ Set.Icc (0:ℝ) 1, Value t 0 dependentQuotient 0 := by
  obtain ⟨t,ht,hz⟩ := certified_curve_zero dependent_curve_certificate.1
    (L := .point (-1/2)) (U := .point (1/2))
    (by norm_num [QInterval.Contains,QInterval.point,dependentQuotient,Expr.realValue])
    (by norm_num [QInterval.Contains,QInterval.point,dependentQuotient,Expr.realValue])
    (by norm_num [QInterval.point]) (by norm_num [QInterval.point])
  exact ⟨t,ht,hz ▸ dependent_curve_certificate.2 t ht⟩

def right : ParameterCell := ⟨⟨1/2,1,by norm_num⟩,by norm_num,by norm_num⟩
def reciprocal : Expr := .div (.const 1) .x

theorem restricted_success : (evalGuarded (X.reparam right) (Y.reparam right) reciprocal).isSome := by
  decide +kernel

theorem restricted_reciprocal_continuous :
    ContinuousOn (fun s => reciprocal.realValue (right.map s) 0) (Set.Icc (0:ℝ) 1) :=
  (evalGuarded_reparam_continuous right continuousOn_id continuousOn_const
    (fun t _ => hx t) (fun t _ => hy t) (Option.some_get restricted_success).symm).1

theorem reciprocal_undefined_at_zero : ¬ ∃ z, Value 0 0 reciprocal z := by
  rintro ⟨z,h⟩
  cases h with
  | div ha hb hn => cases hb; exact hn rfl

def punctured : Set ℝ := {t | t ∈ Set.Icc (0:ℝ) 1 ∧ t ≠ 1/2}
def pole : Expr := .div (.const 1) (.sub .x (.const (1/2)))

theorem punctured_defined (t : ℝ) (ht : t ∈ punctured) : ∃ z, Value t 0 pole z := by
  have hhalf : Value t 0 (.const (1/2)) (1/2:ℝ) := by simpa using (Value.const (x := t) (y := (0:ℝ)) (1/2))
  have hone : Value t 0 (.const 1) 1 := by simpa using (Value.const (x := t) (y := (0:ℝ)) 1)
  exact ⟨1/(t-1/2),Value.div hone (Value.sub Value.x hhalf) (sub_ne_zero.mpr ht.2)⟩

/-- Relative continuity on a punctured set does not certify the missing point. -/
theorem punctured_continuous : ContinuousOn (fun t => pole.realValue t 0) punctured :=
  expr_continuousOn_of_defined continuousOn_id continuousOn_const pole punctured_defined

theorem punctured_opposite_endpoint_signs : pole.realValue 0 0 < 0 ∧ 0 < pole.realValue 1 0 := by
  norm_num [pole,Expr.realValue]

theorem pole_has_no_defined_zero (t : ℝ) : ¬ Value t 0 pole 0 := by
  have h : ∀ z, Value t 0 pole z → z ≠ 0 := by
    intro z hv
    cases hv with
    | div ha hb hn =>
      cases ha
      exact div_ne_zero (by norm_num) hn
  exact fun hv => h 0 hv rfl

theorem pole_midpoint_undefined : ¬ ∃ z, Value (1/2) 0 pole z := by
  rintro ⟨z,hv⟩
  cases hv with
  | div ha hb hn =>
    apply hn
    simpa [Expr.realValue] using value_eq_realValue hb

end GeneralizedIntervalArithmetic.SemanticContinuityExamples
