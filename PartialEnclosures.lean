import LinearIntervals

namespace GeneralizedIntervalArithmetic

/-- Functional bounds may collapse outside a described domain. No continuity
or existence claim is built into value containment. -/
structure FunctionalBounds (α : Type*) where
  lower : α → ℝ
  upper : α → ℝ

def FunctionalBounds.Contains {α : Type*} (I : FunctionalBounds α) (p : α) (z : ℝ) :=
  I.lower p ≤ z ∧ z ≤ I.upper p

/-- Lower and upper approximations to domain membership, not numerical bounds. -/
structure DomainBounds (α : Type*) where
  definite : α → Prop
  possible : α → Prop
  consistent : ∀ p, definite p → possible p

structure PartialEnclosure (α : Type*) where
  values : FunctionalBounds α
  domain : DomainBounds α

/-- Relations express partial values without totalized division. The contract
separates range enclosure, possible definedness, and definite definedness. -/
def PartialEnclosure.Sound {α : Type*} (I : PartialEnclosure α)
    (R : α → ℝ → Prop) : Prop :=
  (∀ p z, R p z → I.values.Contains p z) ∧
  (∀ p z, R p z → I.domain.possible p) ∧
  (∀ p, I.domain.definite p → ∃ z, R p z)

theorem domain_absent {α : Type*} {I : PartialEnclosure α} {R : α → ℝ → Prop}
    (h : I.Sound R) {p : α} (hp : ¬ I.domain.possible p) : ¬ ∃ z, R p z := by
  rintro ⟨z, hz⟩
  exact hp (h.2.1 p z hz)

theorem domain_definite {α : Type*} {I : PartialEnclosure α} {R : α → ℝ → Prop}
    (h : I.Sound R) {p : α} (hp : I.domain.definite p) : ∃ z, R p z := h.2.2 p hp

/-- Sound definite membership forces non-collapsing value bounds there. -/
theorem definite_bounds_ordered {α : Type*} {I : PartialEnclosure α}
    {R : α → ℝ → Prop} (h : I.Sound R) {p : α} (hp : I.domain.definite p) :
    I.values.lower p ≤ I.values.upper p := by
  obtain ⟨z, hz⟩ := domain_definite h hp
  exact (h.1 p z hz).1.trans (h.1 p z hz).2

/-- Collapsing value bounds exclude semantic values, even if domain information
is inconclusive. They do not assert that a primitive operation is total. -/
theorem collapsed_bounds_absent {α : Type*} {I : PartialEnclosure α}
    {R : α → ℝ → Prop} (h : I.Sound R) {p : α}
    (hp : I.values.upper p < I.values.lower p) : ¬ ∃ z, R p z := by
  rintro ⟨z, hz⟩
  exact (not_le_of_gt hp) ((h.1 p z hz).1.trans (h.1 p z hz).2)

/-- A known domain restriction retains both directions of domain information. -/
def PartialEnclosure.restrict {α : Type*} (I : PartialEnclosure α) (D : α → Prop) :
    PartialEnclosure α :=
  ⟨I.values, ⟨fun p => D p ∧ I.domain.definite p,
    fun p => D p ∧ I.domain.possible p, fun p h => ⟨h.1, I.domain.consistent p h.2⟩⟩⟩

theorem restrict_sound {α : Type*} {I : PartialEnclosure α} {R : α → ℝ → Prop}
    (h : I.Sound R) (D : α → Prop) :
    (I.restrict D).Sound (fun p z => D p ∧ R p z) := by
  refine ⟨fun p z hz => h.1 p z hz.2,
    fun p z hz => ⟨hz.1, h.2.1 p z hz.2⟩, ?_⟩
  intro p hp
  obtain ⟨z, hz⟩ := h.2.2 p hp.2
  exact ⟨z, hp.1, hz⟩

def PartialEnclosure.add {α : Type*} (I J : PartialEnclosure α) : PartialEnclosure α :=
  ⟨⟨fun p => I.values.lower p + J.values.lower p,
     fun p => I.values.upper p + J.values.upper p⟩,
   ⟨fun p => I.domain.definite p ∧ J.domain.definite p,
    fun p => I.domain.possible p ∧ J.domain.possible p,
    fun p h => ⟨I.domain.consistent p h.1, J.domain.consistent p h.2⟩⟩⟩

def SumValues {α : Type*} (R S : α → ℝ → Prop) (p : α) (z : ℝ) : Prop :=
  ∃ x y, R p x ∧ S p y ∧ z = x + y

theorem partial_add_sound {α : Type*} {I J : PartialEnclosure α}
    {R S : α → ℝ → Prop} (hI : I.Sound R) (hJ : J.Sound S) :
    (I.add J).Sound (SumValues R S) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro p z ⟨x, y, hx, hy, rfl⟩
    exact ⟨add_le_add (hI.1 p x hx).1 (hJ.1 p y hy).1,
      add_le_add (hI.1 p x hx).2 (hJ.1 p y hy).2⟩
  · rintro p z ⟨x, y, hx, hy, _⟩
    exact ⟨hI.2.1 p x hx, hJ.2.1 p y hy⟩
  · intro p hp
    obtain ⟨x, hx⟩ := hI.2.2 p hp.1
    obtain ⟨y, hy⟩ := hJ.2.2 p hp.2
    exact ⟨x+y, x, y, hx, hy, rfl⟩

/-- Domain and value enclosure do not suffice for an intermediate-value theorem. -/
theorem partial_excludes_zero {α : Type*} {I : PartialEnclosure α}
    {R : α → ℝ → Prop} (h : I.Sound R) {p : α}
    (he : I.values.upper p < 0 ∨ 0 < I.values.lower p) : ¬ R p 0 := by
  intro hr
  rcases he with hn | hp
  · exact (not_le_of_gt hn) (h.1 p 0 hr).2
  · exact (not_le_of_gt hp) (h.1 p 0 hr).1

noncomputable def LinearInterval.partial (I : LinearInterval) : PartialEnclosure ℝ :=
  ⟨⟨I.lower.value, I.upper.value⟩,
   ⟨fun t => t ∈ Set.Icc (0:ℝ) 1, fun t => t ∈ Set.Icc (0:ℝ) 1, fun _ h => h⟩⟩

theorem linear_partial_sound (I : LinearInterval) {f : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, I.Contains t (f t)) :
    I.partial.Sound (fun t z => t ∈ Set.Icc (0:ℝ) 1 ∧ z = f t) := by
  refine ⟨?_, fun _ _ h => h.1, fun t ht => ⟨f t, ht, rfl⟩⟩
  rintro t z ⟨ht, rfl⟩
  exact hf t ht

end GeneralizedIntervalArithmetic
