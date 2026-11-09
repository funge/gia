import NonzeroDomains
import Evaluator
import AuditPolicy

namespace GeneralizedIntervalArithmetic.NonzeroDomainChecks

def one : LinearInterval := .exact ⟨1, 1⟩
def denominator : LinearInterval := .exact ⟨-1/2, 1/2⟩
def Numerator (t z : ℝ) := t ∈ Set.Icc (0:ℝ) 1 ∧ z = 1
def Denominator (t z : ℝ) := t ∈ Set.Icc (0:ℝ) 1 ∧ z = t - 1/2

theorem numerator_sound : one.partial.Sound Numerator := by
  apply linear_partial_sound
  intro t _
  rw [one, linear_exact_contains]
  simp [QAffine.value]

theorem denominator_sound : denominator.partial.Sound Denominator := by
  apply linear_partial_sound
  intro t _
  rw [denominator, linear_exact_contains]
  simp [QAffine.value]
  ring

theorem range_unknown : denominator.recip? = none := by
  norm_num [LinearInterval.recip?, LinearInterval.hull, denominator,
    LinearInterval.exact, QInterval.AwayZero]

theorem domain_exact (t : ℝ) :
    (one.partial.quotientDomain denominator.partial).definite t ↔
      t ∈ Set.Icc (0:ℝ) 1 ∧ t ≠ 1/2 := by
  change (t ∈ Set.Icc (0:ℝ) 1 ∧ t ∈ Set.Icc (0:ℝ) 1 ∧
    ((denominator.upper.value t < 0) ∨ 0 < denominator.upper.value t)) ↔ _
  have hv : denominator.upper.value t = t - 1/2 := by
    simp [denominator, LinearInterval.exact, QAffine.value]; ring
  rw [hv]
  constructor
  · rintro ⟨ht, _, hn | hn⟩ <;> exact ⟨ht, by linarith⟩
  · rintro ⟨ht, hn⟩
    refine ⟨ht, ht, ?_⟩
    rcases lt_or_gt_of_ne hn with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

theorem pole_excluded :
    ¬ (one.partial.quotientDomain denominator.partial).possible (1/2) := by
  norm_num [PartialEnclosure.quotientDomain, DomainBounds.inter,
    PartialEnclosure.nonzero, LinearInterval.partial, denominator,
    LinearInterval.exact, QAffine.value]

theorem quotient_exists {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hn : t ≠ 1/2) :
    ∃ z, QuotientValues Numerator Denominator t z :=
  quotient_domain_definite numerator_sound denominator_sound ((domain_exact t).mpr ⟨ht, hn⟩)

theorem quotient_hole : ¬ ∃ z, QuotientValues Numerator Denominator (1/2) z := by
  rintro ⟨z, hz⟩
  exact pole_excluded (quotient_domain_possible numerator_sound denominator_sound hz)

-- Independent check of the relation, including the nonzero condition.
theorem quotient_semantics (t z : ℝ) :
    QuotientValues Numerator Denominator t z ↔
      t ∈ Set.Icc (0:ℝ) 1 ∧ t ≠ 1/2 ∧ z = 1 / (t - 1/2) := by
  constructor
  · rintro ⟨x, y, ⟨ht, rfl⟩, ⟨_, rfl⟩, hn, rfl⟩
    exact ⟨ht, by intro h; apply hn; rw [h]; ring, rfl⟩
  · rintro ⟨ht, hn, rfl⟩
    exact ⟨1, t - 1/2, ⟨ht, rfl⟩, ⟨ht, rfl⟩, sub_ne_zero.mpr hn, rfl⟩

-- Bridge to the existing partial expression semantics; the domain test is not
-- a replacement value evaluator.
def expression : Expr := .div (.const 1) (.sub .x (.const (1/2)))
theorem expression_bridge {t z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    Value t 0 expression z ↔ QuotientValues Numerator Denominator t z := by
  constructor
  · intro hv
    cases hv with
    | div ha hb hn =>
      cases ha
      cases hb with
      | sub hx hc =>
        cases hx
        cases hc
        refine ⟨1, t - 1/2, ⟨ht, rfl⟩, ⟨ht, rfl⟩, ?_, ?_⟩
        · norm_num at hn ⊢
          exact hn
        · norm_num
  · intro hz
    obtain ⟨_, hn, rfl⟩ := (quotient_semantics t z).mp hz
    have hv := Value.div (x := t) (y := (0:ℝ)) (Value.const 1)
      (Value.sub Value.x (Value.const (1/2))) (by norm_num; exact sub_ne_zero.mpr hn)
    simpa [expression] using hv

-- Identical bounds can describe either zero-only or nonzero-only actual values.
def uncertain : PartialEnclosure Unit :=
  ⟨⟨fun _ => -1, fun _ => 1⟩, ⟨fun _ => True, fun _ => True, fun _ h => h⟩⟩
theorem uncertain_zero_sound : uncertain.Sound (fun _ z => z = 0) := by
  refine ⟨?_, fun _ _ _ => trivial, fun _ _ => ⟨0, rfl⟩⟩
  intro p z hz
  subst z
  norm_num [uncertain, FunctionalBounds.Contains]
theorem uncertain_nonzero_sound : uncertain.Sound (fun _ z => z = 1) := by
  refine ⟨?_, fun _ _ _ => trivial, fun _ _ => ⟨1, rfl⟩⟩
  intro p z hz
  subst z
  norm_num [uncertain, FunctionalBounds.Contains]
theorem inconclusive : uncertain.nonzero.domain.possible () ∧
    ¬ uncertain.nonzero.domain.definite () := by
  norm_num [uncertain, PartialEnclosure.nonzero]

def absent : PartialEnclosure Unit :=
  ⟨⟨fun _ => 1, fun _ => 1⟩, ⟨fun _ => False, fun _ => False, fun _ h => h⟩⟩
theorem absent_stays_absent : ¬ absent.nonzero.domain.possible () := by
  simp [absent, PartialEnclosure.nonzero]

end GeneralizedIntervalArithmetic.NonzeroDomainChecks
#audit_namespace GeneralizedIntervalArithmetic.NonzeroDomainChecks
