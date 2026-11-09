import PointDomains
import QuotientDomains
import AuditPolicy

namespace GeneralizedIntervalArithmetic.PointDomainChecks

def allowed (q : ℚ) := (0 ≤ q ∧ q ≤ 1) ∧ q ≠ 1/4
def domain : DomainBounds ℚ := ⟨allowed, allowed, fun _ h => h⟩
instance (q : ℚ) : Decidable (domain.definite q) :=
  inferInstanceAs (Decidable ((0 ≤ q ∧ q ≤ 1) ∧ q ≠ 1/4))
instance (q : ℚ) : Decidable (domain.possible q) :=
  inferInstanceAs (Decidable ((0 ≤ q ∧ q ≤ 1) ∧ q ≠ 1/4))

def shifted : Expr := .sub .x (.const (1/2))
def reciprocal : Expr := .div (.const 1) shifted
def nested : Expr := .div (.const 1) reciprocal
def zeroTimesPole : Expr := .mul (.const 0) reciprocal
def cancel : Expr := .div shifted shifted
def polynomial : Expr := .add (.mul .x .x) (.const 1)
def query (e : Expr) (q : ℚ) :=
  (inferPointDomain (fun q => q) (fun _ => 0) domain e).classify q
def Actual (e : Expr) (q : ℚ) (z : ℝ) := allowed q ∧ Value (q:ℝ) 0 e z

theorem query_exists {e : Expr} {q : ℚ} (h : query e q = .yes) : ∃ z, Actual e q z := by
  have hc := domain_query_exists (D := inferPointDomain (fun q => q) (fun _ => 0) domain e)
    (inferPointDomain_definite (x := fun q => q) (y := fun _ => 0)
      (D := domain) (E := allowed) (fun _ h => h) e) q h
  simpa [Actual] using hc

theorem query_absent {e : Expr} {q : ℚ} (h : query e q = .no) : ¬ ∃ z, Actual e q z := by
  have hc := domain_query_absent (D := inferPointDomain (fun q => q) (fun _ => 0) domain e)
    (R := fun q z => allowed q ∧ Value (q:ℝ) ((0:ℚ):ℝ) e z)
    (inferPointDomain_possible (x := fun q => q) (y := fun _ => 0)
      (D := domain) (E := allowed) (fun _ h => h) e) q h
  simpa [Actual] using hc

theorem nested_queries :
    ([-1, 0, 1/4, 1/2, 3/4, 1, 2] : List ℚ).map (query nested) =
      [.no, .yes, .no, .no, .yes, .yes, .no] := by decide +kernel

theorem strict_queries :
    query zeroTimesPole (1/2) = .no ∧ query cancel (1/2) = .no ∧
    query zeroTimesPole (3/4) = .yes ∧ query polynomial (3/4) = .yes := by decide +kernel

theorem nested_present : ∃ z, Actual nested (3/4) z := query_exists (by decide +kernel)
theorem nested_pole_absent : ¬ ∃ z, Actual nested (1/2) z := query_absent (by decide +kernel)
theorem nested_external_hole : ¬ ∃ z, Actual nested (1/4) z := query_absent (by decide +kernel)

-- Independent exact partial semantics: double reciprocal cancellation retains its hole.
theorem nested_semantics (t z : ℝ) :
    Value t 0 nested z ↔ t ≠ 1/2 ∧ z = t - 1/2 := by
  constructor
  · intro hv
    cases hv with
    | div ho hi hni =>
      cases ho
      cases hi with
      | div hi hb hnb =>
        cases hi
        cases hb with
        | sub hx hc =>
          cases hx
          cases hc
          norm_num at hnb ⊢
          exact sub_ne_zero.mp hnb
  · rintro ⟨hn, rfl⟩
    have hbase : Value t 0 shifted (t - 1/2) := by
      have h := Value.sub (x := t) (y := (0:ℝ)) Value.x (Value.const (1/2))
      simpa [shifted] using h
    have hi := Value.div (Value.const 1) hbase (sub_ne_zero.mpr hn)
    have hn' : (1:ℝ)/(t - 1/2) ≠ 0 := div_ne_zero one_ne_zero (sub_ne_zero.mpr hn)
    have h := Value.div (Value.const 1) hi (by simpa using hn')
    simpa [nested, reciprocal] using h

theorem nested_defined_iff (q : ℚ) :
    (∃ z, Actual nested q z) ↔ allowed q ∧ q ≠ 1/2 := by
  constructor
  · rintro ⟨z, ha, hv⟩
    have hn := ((nested_semantics (q:ℝ) z).mp hv).1
    refine ⟨ha, ?_⟩
    intro he
    subst q
    norm_num at hn
  · rintro ⟨ha, hn⟩
    refine ⟨(q:ℝ)-1/2, ha, (nested_semantics _ _).mpr ⟨?_, rfl⟩⟩
    intro he
    apply hn
    apply Rat.cast_injective (α := ℝ)
    simpa using he

theorem nested_query_exact (q : ℚ) : query nested q = .yes ↔ allowed q ∧ q ≠ 1/2 := by
  rw [query, domain_query_yes]
  change (allowed q ∧ (eval exactBackend (.point q) (.point 0) nested).isSome = true) ↔ _
  rw [eval_point_defined_iff]
  constructor
  · rintro ⟨ha, z, hz⟩
    exact (nested_defined_iff q).mp ⟨z, ha, by simpa using hz⟩
  · intro h
    obtain ⟨z, ha, hz⟩ := (nested_defined_iff q).mpr h
    exact ⟨ha, z, by simpa using hz⟩

theorem zero_times_undefined_stays_undefined : ¬ ∃ z, Value (1/2) 0 zeroTimesPole z := by
  rintro ⟨z, hv⟩
  cases hv with
  | mul ha hb =>
    cases hb with
    | div ha hb hn =>
      cases hb with
      | sub hx hc =>
        cases hx
        cases hc
        norm_num at hn

-- The old enclosure-based analysis stays conservative; no existing result changes.
def X : LinearInterval := .exact ⟨0, 1⟩
def Y : LinearInterval := .exact ⟨0, 0⟩
theorem previous_analysis_unknown :
    (inferQuotientDomain X Y domain nested).classify (3/4) = .unknown := by decide +kernel

-- Failure on a wide interval cannot be reinterpreted as undefinedness.
def wide : QInterval := ⟨0, 1, by norm_num⟩
theorem wide_unknown : eval exactBackend wide (.point 0) reciprocal = none := by
  norm_num [eval, reciprocal, shifted, combine, exactBackend, guardedDiv, wide,
    QInterval.sub, QInterval.point, QInterval.AwayZero]
theorem wide_contains_defined : wide.Contains (3/4) ∧
    Value (3/4) 0 reciprocal 4 := by
  refine ⟨by norm_num [wide, QInterval.Contains], ?_⟩
  have hb := Value.sub (x := (3/4:ℝ)) (y := (0:ℝ)) Value.x (Value.const (1/2))
  norm_num at hb
  have hv := Value.div (Value.const 1) hb (by norm_num)
  simpa [reciprocal, shifted] using hv

-- Singleton inputs alone are insufficient with a backend allowed to decline.
def declining : Backend := fun _ => none
theorem declining_sound : BackendSound declining := by
  intro I R z h
  cases h
theorem declining_unknown : eval declining (.point 0) (.point 0) (.const 1) = none := rfl
theorem declined_expression_defined : Value 0 0 (.const 1) 1 := by
  simpa using (Value.const (x := (0:ℝ)) (y := (0:ℝ)) 1)

-- External uncertainty is not converted into definite existence by exact arithmetic.
def uncertain : DomainBounds ℚ := ⟨fun _ => False, fun _ => True, fun _ h => h.elim⟩
instance (q : ℚ) : Decidable (uncertain.definite q) := inferInstanceAs (Decidable False)
instance (q : ℚ) : Decidable (uncertain.possible q) := inferInstanceAs (Decidable True)
theorem uncertain_queries :
    (inferPointDomain (fun q => q) (fun _ => 0) uncertain nested).classify (3/4) = .unknown ∧
    (inferPointDomain (fun q => q) (fun _ => 0) uncertain nested).classify (1/2) = .no := by
  decide +kernel

-- Affine rational coordinates agree with the existing real interpretation.
theorem affine_coordinates (a : QAffine) (q : ℚ) :
    (a.valueRat q:ℝ) = a.value (q:ℝ) := affine_valueRat_cast a q

end GeneralizedIntervalArithmetic.PointDomainChecks
#audit_namespace GeneralizedIntervalArithmetic.PointDomainChecks
