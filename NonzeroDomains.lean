import LinearDivision

namespace GeneralizedIntervalArithmetic

/-- Numerical evidence for restricting a partial relation to its nonzero values.
Crossing zero is inconclusive; collapsed zero bounds exclude all nonzero values.
The input domain is retained, even when numerical bounds exclude zero. -/
def PartialEnclosure.nonzero {α : Type*} (I : PartialEnclosure α) : PartialEnclosure α :=
  ⟨I.values,
   ⟨fun p => I.domain.definite p ∧
      (I.values.upper p < 0 ∨ 0 < I.values.lower p),
    fun p => I.domain.possible p ∧
      (I.values.lower p ≠ 0 ∨ I.values.upper p ≠ 0),
    fun p h => ⟨I.domain.consistent p h.1, by
      rcases h.2 with h | h
      · exact Or.inr (ne_of_lt h)
      · exact Or.inl (ne_of_gt h)⟩⟩⟩

theorem nonzero_sound {α : Type*} {I : PartialEnclosure α} {R : α → ℝ → Prop}
    (h : I.Sound R) : I.nonzero.Sound (fun p z => R p z ∧ z ≠ 0) := by
  refine ⟨fun p z hz => h.1 p z hz.1, ?_, ?_⟩
  · intro p z hz
    refine ⟨h.2.1 p z hz.1, ?_⟩
    by_contra hn
    push_neg at hn
    have hb := h.1 p z hz.1
    exact hz.2 (le_antisymm (hn.2 ▸ hb.2) (hn.1 ▸ hb.1))
  · intro p hp
    obtain ⟨z, hz⟩ := h.2.2 p hp.1
    refine ⟨z, hz, ?_⟩
    intro he
    subst z
    exact partial_excludes_zero h hp.2 hz

/-- Only a domain description: no quotient range or continuity claim is made.
Operands retain the independent witnesses of `QuotientValues`. -/
def PartialEnclosure.quotientDomain {α : Type*} (I J : PartialEnclosure α) : DomainBounds α :=
  I.domain.inter J.nonzero.domain

theorem quotient_domain_possible {α : Type*} {I J : PartialEnclosure α}
    {A B : α → ℝ → Prop} (hI : I.Sound A) (hJ : J.Sound B)
    {p : α} {z : ℝ} (hz : QuotientValues A B p z) :
    (I.quotientDomain J).possible p := by
  obtain ⟨x, y, hx, hy, hn, _⟩ := hz
  exact ⟨hI.2.1 p x hx, (nonzero_sound hJ).2.1 p y ⟨hy, hn⟩⟩

theorem quotient_domain_definite {α : Type*} {I J : PartialEnclosure α}
    {A B : α → ℝ → Prop} (hI : I.Sound A) (hJ : J.Sound B)
    {p : α} (hp : (I.quotientDomain J).definite p) :
    ∃ z, QuotientValues A B p z := by
  obtain ⟨x, hx⟩ := hI.2.2 p hp.1
  obtain ⟨y, hy, hn⟩ := (nonzero_sound hJ).2.2 p hp.2
  exact ⟨x / y, x, y, hx, hy, hn, rfl⟩

end GeneralizedIntervalArithmetic
