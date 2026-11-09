import DomainQueries
import AuditPolicy

namespace GeneralizedIntervalArithmetic.DomainQueryChecks

def unitDomain : DomainBounds ℚ :=
  ⟨fun q => 0 ≤ q ∧ q ≤ 1, fun q => 0 ≤ q ∧ q ≤ 1, fun _ h => h⟩
def punctured : DomainBounds ℚ :=
  ⟨fun q => q ≠ 1/2 ∧ q ≠ 1/4, fun q => q ≠ 1/2 ∧ q ≠ 1/4, fun _ h => h⟩
def domain : DomainBounds ℚ := unitDomain.inter punctured

instance (q : ℚ) : Decidable (domain.definite q) :=
  inferInstanceAs (Decidable ((0 ≤ q ∧ q ≤ 1) ∧ q ≠ 1/2 ∧ q ≠ 1/4))
instance (q : ℚ) : Decidable (domain.possible q) :=
  inferInstanceAs (Decidable ((0 ≤ q ∧ q ≤ 1) ∧ q ≠ 1/2 ∧ q ≠ 1/4))

def query (q : ℚ) : BranchDecision := domain.classify q

def expression : Expr := .div (.const 1) (.sub .x (.const (1/2)))
def Actual (q : ℚ) (z : ℝ) : Prop :=
  domain.definite q ∧ Value (q:ℝ) 0 expression z

-- Independent closed-form check of the original partial expression.
theorem expression_semantics (q : ℚ) (z : ℝ) :
    Value (q:ℝ) 0 expression z ↔
      (q:ℝ) ≠ 1/2 ∧ z = 1 / ((q:ℝ) - 1/2) := by
  constructor
  · intro hv
    cases hv with
    | div ha hb hn =>
      cases ha
      cases hb with
      | sub hx hc =>
        cases hx
        cases hc
        norm_num at hn ⊢
        exact sub_ne_zero.mp hn
  · rintro ⟨hn, rfl⟩
    have hv := Value.div (x := (q:ℝ)) (y := (0:ℝ)) (Value.const 1)
      (Value.sub Value.x (Value.const (1/2))) (by norm_num; exact sub_ne_zero.mpr hn)
    simpa [expression] using hv

-- Functional bounds are a semantic fixture, not a computed reciprocal enclosure.
noncomputable def enclosure : PartialEnclosure ℚ :=
  ⟨⟨fun q => 1 / ((q:ℝ) - 1/2), fun q => 1 / ((q:ℝ) - 1/2)⟩, domain⟩

theorem enclosure_sound : enclosure.Sound Actual := by
  refine ⟨?_, fun _ _ hz => hz.1, ?_⟩
  · intro q z hz
    have he := ((expression_semantics q z).mp hz.2).2
    subst z
    exact ⟨le_rfl, le_rfl⟩
  · intro q hq
    refine ⟨1 / ((q:ℝ) - 1/2), hq, (expression_semantics q _).mpr ⟨?_, rfl⟩⟩
    have hn : q ≠ (1/2:ℚ) := hq.2.1
    intro he
    apply hn
    apply Rat.cast_injective (α := ℝ)
    simpa using he

theorem computed_queries :
    ([-1, 0, 1/4, 1/2, 3/4, 1, 2] : List ℚ).map query =
      [.no, .yes, .no, .no, .yes, .yes, .no] := by decide +kernel

-- The same exact classification theorem works at any rational query, not just samples.
theorem query_yes_iff (q : ℚ) : query q = .yes ↔
    (0 ≤ q ∧ q ≤ 1) ∧ q ≠ 1/2 ∧ q ≠ 1/4 := domain_query_yes domain q

theorem certified_value : ∃ z, Actual (3/4) z :=
  domain_query_exists (D := domain) enclosure_sound.2.2 (3/4) (by decide +kernel)
theorem excluded_pole : ¬ ∃ z, Actual (1/2) z :=
  domain_query_absent (D := domain) enclosure_sound.2.1 (1/2) (by decide +kernel)
theorem excluded_input_hole : ¬ ∃ z, Actual (1/4) z :=
  domain_query_absent (D := domain) enclosure_sound.2.1 (1/4) (by decide +kernel)
theorem excluded_outside : ¬ ∃ z, Actual 2 z :=
  domain_query_absent (D := domain) enclosure_sound.2.1 2 (by decide +kernel)

-- The input hole is not an arithmetic pole: the unrestricted expression has a value.
theorem input_hole_expression_defined : Value (1/4) 0 expression (-4) := by
  have h := (expression_semantics (1/4) (-4)).mpr (by norm_num)
  norm_num at h
  exact h

-- Unknown is compatible with both absent and present semantic relations.
def uncertain : DomainBounds Unit := ⟨fun _ => False, fun _ => True, fun _ h => h.elim⟩
instance : Decidable (uncertain.definite ()) := inferInstanceAs (Decidable False)
instance : Decidable (uncertain.possible ()) := inferInstanceAs (Decidable True)
theorem computed_unknown : uncertain.classify () = .unknown := by decide +kernel
noncomputable def uncertainEnclosure : PartialEnclosure Unit :=
  ⟨⟨fun _ => 0, fun _ => 0⟩, uncertain⟩
theorem unknown_empty_sound : uncertainEnclosure.Sound (fun _ _ => False) :=
  ⟨fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ h => h.elim⟩
theorem unknown_present_sound : uncertainEnclosure.Sound (fun _ z => z = 0) := by
  refine ⟨?_, fun _ _ _ => trivial, fun _ h => h.elim⟩
  rintro p z rfl
  exact ⟨le_rfl, le_rfl⟩

end GeneralizedIntervalArithmetic.DomainQueryChecks
#audit_namespace GeneralizedIntervalArithmetic.DomainQueryChecks
