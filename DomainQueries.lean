import PiecewiseSelection

namespace GeneralizedIntervalArithmetic

/-- Query existing domain evidence at one parameter. Execution requires actual
Decidable instances for both predicates; this is not an oracle for real domains.
The existing three-way result is reused, with pointwise domain semantics. -/
def DomainBounds.classify {α : Type*} (D : DomainBounds α) (p : α)
    [Decidable (D.definite p)] [Decidable (D.possible p)] : BranchDecision :=
  if D.definite p then .yes else if D.possible p then .unknown else .no

theorem domain_query_yes {α : Type*} (D : DomainBounds α) (p : α)
    [Decidable (D.definite p)] [Decidable (D.possible p)] :
    D.classify p = .yes ↔ D.definite p := by
  unfold DomainBounds.classify
  split <;> simp_all
  split <;> simp_all

theorem domain_query_no {α : Type*} (D : DomainBounds α) (p : α)
    [Decidable (D.definite p)] [Decidable (D.possible p)] :
    D.classify p = .no ↔ ¬ D.possible p := by
  unfold DomainBounds.classify
  split
  · rename_i h
    simp [D.consistent p h]
  · split <;> simp_all

theorem domain_query_unknown {α : Type*} (D : DomainBounds α) (p : α)
    [Decidable (D.definite p)] [Decidable (D.possible p)] :
    D.classify p = .unknown ↔ D.possible p ∧ ¬ D.definite p := by
  unfold DomainBounds.classify
  split <;> simp_all

/-- Consume domain-only existence evidence; a finite value enclosure is not needed. -/
theorem domain_query_exists {α : Type*} {D : DomainBounds α}
    {R : α → ℝ → Prop} (hD : ∀ p, D.definite p → ∃ z, R p z) (p : α)
    [Decidable (D.definite p)] [Decidable (D.possible p)]
    (hc : D.classify p = .yes) : ∃ z, R p z :=
  hD p ((domain_query_yes D p).mp hc)

/-- Consume domain-only exclusion evidence, independently of value bounds. -/
theorem domain_query_absent {α : Type*} {D : DomainBounds α}
    {R : α → ℝ → Prop} (hD : ∀ p z, R p z → D.possible p) (p : α)
    [Decidable (D.definite p)] [Decidable (D.possible p)]
    (hc : D.classify p = .no) : ¬ ∃ z, R p z := by
  rintro ⟨z, hz⟩
  exact ((domain_query_no D p).mp hc) (hD p z hz)

end GeneralizedIntervalArithmetic
