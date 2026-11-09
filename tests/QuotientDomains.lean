import QuotientDomains
import AuditPolicy

namespace GeneralizedIntervalArithmetic.QuotientDomainChecks

def X : LinearInterval := .exact ⟨0, 1⟩
def Y : LinearInterval := .exact ⟨0, 0⟩
def allowed (q : ℚ) := (0 ≤ q ∧ q ≤ 1) ∧ q ≠ 1/4
def domain : DomainBounds ℚ := ⟨allowed, allowed, fun _ h => h⟩
instance (q : ℚ) : Decidable (domain.definite q) :=
  inferInstanceAs (Decidable ((0 ≤ q ∧ q ≤ 1) ∧ q ≠ 1/4))
instance (q : ℚ) : Decidable (domain.possible q) :=
  inferInstanceAs (Decidable ((0 ≤ q ∧ q ≤ 1) ∧ q ≠ 1/4))

def shifted : Expr := .sub .x (.const (1/2))
def reciprocal : Expr := .div (.const 1) shifted
def cancellation : Expr := .div shifted shifted
def nested : Expr := .div (.const 1) reciprocal
def zeroDenominator : Expr := .div (.const 1) (.sub .x .x)
def polynomial : Expr := .add .x (.const 1)

def query (e : Expr) (q : ℚ) : BranchDecision :=
  (inferQuotientDomain X Y domain e).classify q

def Actual (e : Expr) (q : ℚ) (z : ℝ) := allowed q ∧ Value (q:ℝ) 0 e z

private theorem inputs (q : ℚ) (hq : allowed q) :
    (q:ℝ) ∈ Set.Icc (0:ℝ) 1 ∧ X.Contains (q:ℝ) (q:ℝ) ∧ Y.Contains (q:ℝ) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · exact_mod_cast hq.1.1
    · exact_mod_cast hq.1.2
  · rw [X, linear_exact_contains]
    simp [QAffine.value]
  · rw [Y, linear_exact_contains]
    simp [QAffine.value]

theorem query_exists {e : Expr} {q : ℚ} (h : query e q = .yes) : ∃ z, Actual e q z :=
  domain_query_exists (D := inferQuotientDomain X Y domain e)
    (inferQuotientDomain_definite (X := X) (Y := Y) (D := domain)
      (E := allowed) (x := fun q => (q:ℝ)) (y := fun _ => 0) (fun _ h => h) (fun _ h => h) inputs e) q h

theorem query_absent {e : Expr} {q : ℚ} (h : query e q = .no) : ¬ ∃ z, Actual e q z :=
  domain_query_absent (D := inferQuotientDomain X Y domain e) (R := Actual e)
    (inferQuotientDomain_possible (X := X) (Y := Y) (D := domain)
      (E := allowed) (x := fun q => (q:ℝ)) (y := fun _ => 0) (fun _ h => h) (fun _ h => h) inputs e) q h

theorem reciprocal_queries :
    ([-1, 0, 1/4, 1/2, 3/4, 1, 2] : List ℚ).map (query reciprocal) =
      [.no, .yes, .no, .no, .yes, .yes, .no] := by decide +kernel

theorem reciprocal_query_exact (q : ℚ) :
    query reciprocal q = .yes ↔ allowed q ∧ q ≠ 1/2 := by
  rw [query, domain_query_yes]
  norm_num [inferQuotientDomain, reciprocal, shifted, evalGuarded, combineLinear, X, Y,
    quotientDomainRat, LinearInterval.sub, QAffine.sub, QAffine.valueRat, domain,
    LinearInterval.exact]
  intro _
  constructor <;> intro h he <;> apply h <;> linarith

theorem cancellation_queries :
    ([0, 1/4, 1/2, 3/4, 1] : List ℚ).map (query cancellation) =
      [.yes, .no, .no, .yes, .yes] := by decide +kernel

theorem reciprocal_value : ∃ z, Actual reciprocal (3/4) z := query_exists (by decide +kernel)
theorem pole_absent : ¬ ∃ z, Actual reciprocal (1/2) z := query_absent (by decide +kernel)
theorem hole_absent : ¬ ∃ z, Actual reciprocal (1/4) z := query_absent (by decide +kernel)
theorem no_cancelled_pole : ¬ ∃ z, Actual cancellation (1/2) z := query_absent (by decide +kernel)
theorem collapsed_zero_absent : ¬ ∃ z, Actual zeroDenominator (3/4) z :=
  query_absent (by decide +kernel)

-- Independent direct semantic derivations; no inference result supplies these.
theorem reciprocal_at (q : ℚ) (hn : q ≠ 1/2) :
    Value (q:ℝ) 0 reciprocal (1 / ((q:ℝ) - 1/2)) := by
  have hn' : (q:ℝ) ≠ 1/2 := by
    intro h
    apply hn
    apply Rat.cast_injective (α := ℝ)
    simpa using h
  have hv := Value.div (x := (q:ℝ)) (y := (0:ℝ)) (Value.const 1)
    (Value.sub Value.x (Value.const (1/2))) (by norm_num; exact sub_ne_zero.mpr hn')
  simpa [reciprocal, shifted] using hv

theorem input_hole_is_not_pole : Value (1/4) 0 reciprocal (-4) := by
  have h := reciprocal_at (1/4) (by norm_num)
  norm_num at h
  exact h

theorem actual_pole_undefined : ¬ ∃ z, Value (1/2) 0 reciprocal z := by
  rintro ⟨z, hv⟩
  cases hv with
  | div ha hb hn =>
    cases hb with
    | sub hx hc =>
      cases hx
      cases hc
      norm_num at hn

theorem reciprocal_defined_iff (q : ℚ) :
    (∃ z, Actual reciprocal q z) ↔ allowed q ∧ q ≠ 1/2 := by
  constructor
  · rintro ⟨z, hA, hv⟩
    refine ⟨hA, ?_⟩
    intro hq
    subst q
    exact actual_pole_undefined ⟨z, by simpa using hv⟩
  · rintro ⟨hA, hn⟩
    exact ⟨_, hA, reciprocal_at q hn⟩

theorem nested_queries :
    ([0, 1/4, 1/2, 3/4] : List ℚ).map (query nested) =
      [.unknown, .no, .unknown, .unknown] := by decide +kernel

theorem nested_present_despite_unknown : Actual nested (3/4) (1/4) := by
  refine ⟨by norm_num [allowed], ?_⟩
  have hv := reciprocal_at (3/4) (by norm_num)
  norm_num at hv
  have h := Value.div (x := (3/4:ℝ)) (y := (0:ℝ)) (Value.const 1) hv (by norm_num)
  simpa [nested] using h

theorem nested_absent_despite_unknown : ¬ ∃ z, Value (1/2) 0 nested z := by
  rintro ⟨z, hv⟩
  cases hv with
  | div ha hb hn => exact actual_pole_undefined ⟨_, hb⟩

theorem unsupported_queries : query polynomial (3/4) = .unknown ∧
    query polynomial (1/4) = .no := by decide +kernel

theorem unsupported_is_defined : Value (3/4) 0 polynomial (7/4) := by
  have hv := Value.add (x := (3/4:ℝ)) (y := (0:ℝ)) Value.x (Value.const 1)
  norm_num at hv
  exact hv

-- Successful child evaluation can still leave numerical nonzero evidence unresolved.
def wide : LinearInterval := .constant ⟨-1, 1, by norm_num⟩
def wideQuotient : Expr := .div (.const 1) .x
def wideQuery (q : ℚ) : BranchDecision :=
  (inferQuotientDomain wide Y domain wideQuotient).classify q
theorem crossing_zero_unknown : wideQuery (1/2) = .unknown := by decide +kernel

theorem wide_allows_zero : wide.Contains (1/2) 0 := by
  rw [wide, linear_constant_contains]
  norm_num [QInterval.Contains]
theorem wide_allows_nonzero : wide.Contains (1/2) (1/2) := by
  rw [wide, linear_constant_contains]
  norm_num [QInterval.Contains]
theorem wide_defined_instance : Value (1/2) 0 wideQuotient 2 := by
  have hv := Value.div (x := (1/2:ℝ)) (y := (0:ℝ)) (Value.const 1) Value.x (by norm_num)
  norm_num at hv
  exact hv
theorem wide_undefined_instance : ¬ ∃ z, Value 0 0 wideQuotient z := by
  rintro ⟨z, hv⟩
  cases hv with
  | div ha hb hn => cases hb; exact hn rfl

end GeneralizedIntervalArithmetic.QuotientDomainChecks
#audit_namespace GeneralizedIntervalArithmetic.QuotientDomainChecks
