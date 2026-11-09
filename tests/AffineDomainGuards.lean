import AffineDomainGuards
import AuditPolicy

namespace GeneralizedIntervalArithmetic.AffineGuardChecks

def a : RationalAffineForm := ⟨1, 0, -1⟩
def b : RationalAffineForm := ⟨1, 0, 1⟩
def allowed (p : ℚ × ℚ) := (p.1 = -1 ∨ p.1 = 1) ∧ p.2 = 0
def discrete : DomainBounds (ℚ × ℚ) := ⟨allowed, allowed, fun _ h => h⟩
instance (p : ℚ × ℚ) : Decidable (discrete.definite p) :=
  inferInstanceAs (Decidable ((p.1 = -1 ∨ p.1 = 1) ∧ p.2 = 0))
instance (p : ℚ × ℚ) : Decidable (discrete.possible p) :=
  inferInstanceAs (Decidable ((p.1 = -1 ∨ p.1 = 1) ∧ p.2 = 0))

def discreteQuery (gs : List RationalAffineForm) (p : ℚ × ℚ) :=
  (affineGuardDomain gs discrete).classify p

theorem disjoint_queries :
    discreteQuery [a] (-1,0) = .yes ∧ discreteQuery [b] (1,0) = .yes ∧
    discreteQuery [a,b] (-1,0) = .no ∧ discreteQuery [a,b] (1,0) = .no ∧
    discreteQuery [a,b] (0,0) = .no := by decide +kernel

-- Quantifiers are over real environments here, not a finite set of sampled queries.
theorem each_child_has_input :
    (∃ x z, (x = -1 ∨ x = 1) ∧ Value x 0 (affineReciprocalSum [a]) z) ∧
    (∃ x z, (x = -1 ∨ x = 1) ∧ Value x 0 (affineReciprocalSum [b]) z) := by
  constructor
  · obtain ⟨z, hz⟩ := (affine_sum_defined_iff [a] ((-1:ℝ),0)).mpr (by
      simp [a, RationalAffineForm.value])
    exact ⟨-1,z,Or.inl rfl,hz⟩
  · obtain ⟨z, hz⟩ := (affine_sum_defined_iff [b] ((1:ℝ),0)).mpr (by
      simp [b, RationalAffineForm.value])
    exact ⟨1,z,Or.inr rfl,hz⟩

theorem no_shared_input :
    ¬ ∃ x z, (x = -1 ∨ x = 1) ∧ Value x 0 (affineReciprocalSum [a,b]) z := by
  rintro ⟨x,z,hx,hv⟩
  have h := (affine_sum_defined_iff [a,b] (x,0)).mp ⟨z,hv⟩
  rcases hx with rfl | rfl <;> simp [a,b,RationalAffineForm.value] at h

theorem excluded_midpoint_is_defined : ∃ z, Value 0 0 (affineReciprocalSum [a,b]) z :=
  (affine_sum_defined_iff [a,b] (0,0)).mpr (by simp [a,b,RationalAffineForm.value])

def c : RationalAffineForm := ⟨1, 1, -1⟩
def d : RationalAffineForm := ⟨1, -1, 0⟩
def allInputs : DomainBounds (ℚ × ℚ) := ⟨fun _ => True, fun _ => True, fun _ h => h⟩
instance (p : ℚ × ℚ) : Decidable (allInputs.definite p) := inferInstanceAs (Decidable True)
instance (p : ℚ × ℚ) : Decidable (allInputs.possible p) := inferInstanceAs (Decidable True)
def query (gs : List RationalAffineForm) (p : ℚ × ℚ) := (affineGuardDomain gs allInputs).classify p

theorem two_coordinate_queries :
    ([(2,0),(1/2,1/2),(1,0),(1,1),(0,2)] : List (ℚ × ℚ)).map (query [c,d]) =
      [.yes,.no,.no,.no,.yes] := by decide +kernel

theorem two_coordinate_semantics (x y : ℝ) :
    (∃ z, Value x y (affineReciprocalSum [c,d]) z) ↔
      x+y ≠ 1 ∧ x ≠ y := by
  rw [affine_sum_defined_iff [c,d] (x,y)]
  simp [c,d,RationalAffineForm.value,sub_ne_zero,sub_eq_add_neg]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> intro h
  · apply h1; linarith
  · apply h2; linarith
  · apply h1; linarith
  · apply h2; linarith

-- Direct Value construction, independent of the guard query result.
theorem concrete_value : Value 2 0 (affineReciprocalSum [c,d]) (3/2) := by
  have hc := affine_form_value c ((2:ℝ),0)
  have hd := affine_form_value d ((2:ℝ),0)
  norm_num [c,d,RationalAffineForm.value] at hc hd
  have vc := Value.div (Value.const 1) hc (by norm_num)
  have vd := Value.div (Value.const 1) hd (by norm_num)
  have hz := Value.add vc (Value.add vd (Value.const 0))
  norm_num at hz
  simpa [affineReciprocalSum,c,d] using hz

theorem query_supplies_value : ∃ z, True ∧ Value 2 0 (affineReciprocalSum [c,d]) z := by
  have h := domain_query_exists (D := affineGuardDomain [c,d] allInputs)
    (affine_guard_domain_definite (D := allInputs) (E := fun _ => True) (fun _ _ => trivial) [c,d])
    (2,0) (by decide +kernel)
  simpa using h

theorem query_excludes_pole : ¬ ∃ z, True ∧ Value 1 0 (affineReciprocalSum [c,d]) z := by
  have h := domain_query_absent (D := affineGuardDomain [c,d] allInputs)
    (R := fun p z => True ∧ Value (p.1:ℝ) (p.2:ℝ) (affineReciprocalSum [c,d]) z)
    (affine_guard_domain_possible (D := allInputs) (E := fun _ => True) (fun _ _ => trivial) [c,d])
    (1,0) (by decide +kernel)
  simpa using h

def uncertain : DomainBounds (ℚ × ℚ) := ⟨fun _ => False, fun _ => True, fun _ h => h.elim⟩
instance (p : ℚ × ℚ) : Decidable (uncertain.definite p) := inferInstanceAs (Decidable False)
instance (p : ℚ × ℚ) : Decidable (uncertain.possible p) := inferInstanceAs (Decidable True)
theorem uncertainty_retained :
    (affineGuardDomain [c,d] uncertain).classify (2,0) = .unknown ∧
    (affineGuardDomain [c,d] uncertain).classify (1,0) = .no := by decide +kernel

def zeroForm : RationalAffineForm := ⟨0,0,0⟩
theorem degenerate_and_empty_queries : query [] (0,0) = .yes ∧
    query [zeroForm] (2,0) = .no ∧ query [c,c] (2,0) = .yes := by decide +kernel

theorem zero_denominator_undefined (x y : ℝ) :
    ¬ ∃ z, Value x y (affineReciprocalSum [zeroForm]) z := by
  rw [affine_sum_defined_iff [zeroForm] (x,y)]
  simp [zeroForm,RationalAffineForm.value]

end GeneralizedIntervalArithmetic.AffineGuardChecks
#audit_namespace GeneralizedIntervalArithmetic.AffineGuardChecks
