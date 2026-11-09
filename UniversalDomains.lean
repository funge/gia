import GuardedEvaluator

namespace GeneralizedIntervalArithmetic

/-- Compatibility of actual definedness with a Boolean interval of domain
information. Unknown permits either outcome; definite true requires definedness.
This is the optimistic equivalence reading, not optimistic truth as existence. -/
def DomainBounds.Compatible {α : Type*} (D : DomainBounds α) (p : α) (P : Prop) : Prop :=
  (D.definite p → P) ∧ (P → D.possible p)

theorem domain_compatible_true {α : Type*} (D : DomainBounds α) (p : α) :
    D.Compatible p True ↔ D.possible p := by
  simp [DomainBounds.Compatible]

theorem domain_compatible_false {α : Type*} (D : DomainBounds α) (p : α) :
    D.Compatible p False ↔ ¬ D.definite p := by
  simp [DomainBounds.Compatible]

/-- Each represented input gets its own domain obligation. The same input
witness must be retained by subsequent composition. -/
def PartialEnclosure.UniversalSound {α W : Type*} (I : PartialEnclosure α)
    (A : α → W → Prop) (R : α → W → ℝ → Prop) : Prop :=
  ∀ p w, A p w →
    (∀ z, R p w z → I.values.Contains p z) ∧
    I.domain.Compatible p (∃ z, R p w z)

/-- Recover the existing existential contract only when definite parameters
actually have represented inputs. This premise prevents vacuous totality. -/
theorem universal_projects {α W : Type*} {I : PartialEnclosure α}
    {A : α → W → Prop} {R : α → W → ℝ → Prop}
    (h : I.UniversalSound A R)
    (hne : ∀ p, I.domain.definite p → ∃ w, A p w) :
    I.Sound (fun p z => ∃ w, A p w ∧ R p w z) := by
  refine ⟨?_,?_,?_⟩
  · rintro p z ⟨w,hw,hz⟩
    exact (h p w hw).1 z hz
  · rintro p z ⟨w,hw,hz⟩
    exact (h p w hw).2.2 ⟨z,hz⟩
  · intro p hp
    obtain ⟨w,hw⟩ := hne p hp
    obtain ⟨z,hz⟩ := (h p w hw).2.1 hp
    exact ⟨z,w,hw,hz⟩

/-- Exact Boolean domain envelope. The nonempty-input guard resolves empty
fibers explicitly rather than allowing a vacuous definite assertion. -/
def exactInputDomain {α W : Type*} (A : α → W → Prop)
    (R : α → W → ℝ → Prop) : DomainBounds α :=
  ⟨fun p => (∃ w, A p w) ∧ ∀ w, A p w → ∃ z, R p w z,
   fun p => ∃ w z, A p w ∧ R p w z,
   by
     rintro p ⟨⟨w,hw⟩,h⟩
     obtain ⟨z,hz⟩ := h w hw
     exact ⟨w,z,hw,hz⟩⟩

/-- On nonempty input fibers, exact lower domain means every input is defined. -/
theorem exact_input_definite_iff {α W : Type*} (A : α → W → Prop)
    (R : α → W → ℝ → Prop) (p : α) (hne : ∃ w, A p w) :
    (exactInputDomain A R).definite p ↔ ∀ w, A p w → ∃ z, R p w z :=
  ⟨And.right,fun h => ⟨hne,h⟩⟩

theorem exact_input_universal {α W : Type*} {V : FunctionalBounds α}
    {A : α → W → Prop} {R : α → W → ℝ → Prop}
    (hv : ∀ p w, A p w → ∀ z, R p w z → V.Contains p z) :
    (PartialEnclosure.mk V (exactInputDomain A R)).UniversalSound A R := by
  intro p w hw
  exact ⟨hv p w hw,fun h => h.2 w hw,fun ⟨z,hz⟩ => ⟨w,z,hw,hz⟩⟩

/-- The exact envelope is more informative than any universally valid domain
on nonempty fibers: its definite set is larger, its possible set smaller. -/
theorem exact_input_domain_precision {α W : Type*} {I : PartialEnclosure α}
    {A : α → W → Prop} {R : α → W → ℝ → Prop}
    (h : I.UniversalSound A R) (p : α) (hne : ∃ w, A p w) :
    (I.domain.definite p → (exactInputDomain A R).definite p) ∧
    ((exactInputDomain A R).possible p → I.domain.possible p) := by
  constructor
  · intro hd
    exact ⟨hne,fun w hw => (h p w hw).2.1 hd⟩
  · rintro ⟨w,z,hw,hz⟩
    exact (h p w hw).2.2 ⟨z,hz⟩

/-- Addition preserves the stronger contract at the SAME represented input.
Existential projections are deliberately not composed independently. -/
theorem universal_add_sound {α W : Type*} {I J : PartialEnclosure α}
    {A : α → W → Prop} {R S : α → W → ℝ → Prop}
    (hI : I.UniversalSound A R) (hJ : J.UniversalSound A S) :
    (I.add J).UniversalSound A (fun p w z =>
      ∃ x y, R p w x ∧ S p w y ∧ z = x+y) := by
  intro p w hw
  obtain ⟨hi,hdi,hpi⟩ := hI p w hw
  obtain ⟨hj,hdj,hpj⟩ := hJ p w hw
  refine ⟨?_,?_,?_⟩
  · rintro z ⟨x,y,hx,hy,rfl⟩
    exact ⟨add_le_add (hi x hx).1 (hj y hy).1,
      add_le_add (hi x hx).2 (hj y hy).2⟩
  · intro h
    obtain ⟨x,hx⟩ := hdi h.1
    obtain ⟨y,hy⟩ := hdj h.2
    exact ⟨x+y,x,y,hx,hy,rfl⟩
  · rintro ⟨z,x,y,hx,hy,_⟩
    exact ⟨hpi ⟨x,hx⟩,hpj ⟨y,hy⟩⟩

/-- Preserve an external domain exactly, including all holes. -/
theorem universal_restrict_sound {α W : Type*} {I : PartialEnclosure α}
    {A : α → W → Prop} {R : α → W → ℝ → Prop}
    (h : I.UniversalSound A R) (E : α → Prop) :
    (I.restrict E).UniversalSound A (fun p w z => E p ∧ R p w z) := by
  intro p w hw
  refine ⟨fun z hz => (h p w hw).1 z hz.2,?_,?_⟩
  · intro hp
    obtain ⟨z,hz⟩ := (h p w hw).2.1 hp.2
    exact ⟨z,hp.1,hz⟩
  · rintro ⟨z,he,hz⟩
    exact ⟨he,(h p w hw).2.2 ⟨z,hz⟩⟩

/-- A successful guarded interpretation certifies EVERY enclosed coordinate
pair on the external domain, including guarded nonzero denominators. -/
theorem evalGuarded_universal_sound {X Y V : LinearInterval} {e : Expr}
    (E : ℝ → Prop) (A : ℝ → (ℝ × ℝ) → Prop)
    (hx : ∀ t w, A t w → E t → t ∈ Set.Icc (0:ℝ) 1 → X.Contains t w.1)
    (hy : ∀ t w, A t w → E t → t ∈ Set.Icc (0:ℝ) 1 → Y.Contains t w.2)
    (hr : evalGuarded X Y e = some V) :
    (V.partial.restrict E).UniversalSound A
      (fun t w z => E t ∧ t ∈ Set.Icc (0:ℝ) 1 ∧ Value w.1 w.2 e z) := by
  intro t w hw
  refine ⟨?_,?_,?_⟩
  · rintro z ⟨he,ht,hz⟩
    exact evalGuarded_sound ht (hx t w hw he ht) (hy t w hw he ht) hz hr
  · rintro ⟨he,ht⟩
    obtain ⟨z,hz⟩ := evalGuarded_defined ht (hx t w hw he ht) (hy t w hw he ht) hr
    exact ⟨z,he,ht,hz⟩
  · rintro ⟨z,he,ht,_⟩
    exact ⟨he,ht⟩

end GeneralizedIntervalArithmetic
