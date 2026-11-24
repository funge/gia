import FamilyDemotion
import DomainConstraints

/-! Semantic demotion of arbitrary representations of real-valued families.
Values and domain classifications are separate obligations. -/
namespace GeneralizedIntervalArithmetic.GeneralFamilyDemotion

/-- Set-valued version of UniversalSound, allowing non-interval representations.
Each admitted input keeps its own definedness obligation at the same parameter. -/
def Sound {α W : Type*} (V : α → Set ℝ) (D : DomainBounds α)
    (A : α → W → Prop) (R : α → W → ℝ → Prop) : Prop :=
  ∀ p w, A p w → (∀ z, R p w z → z ∈ V p) ∧ D.Compatible p (∃ z, R p w z)

/-- Numeric inclusion is needed only where a defined value is possible.
Classification weakening is an additional, independent premise. -/
def Demotes {α : Type*} (V : α → Set ℝ) (D : DomainBounds α)
    (V' : α → Set ℝ) (D' : DomainBounds α) : Prop :=
  DomainConstraints.Refines D D' ∧ ∀ p, D.possible p → V p ⊆ V' p

theorem sound_partial_iff {α W : Type*} (I : PartialEnclosure α)
    (A : α → W → Prop) (R : α → W → ℝ → Prop) :
    Sound (fun p => {z | I.values.Contains p z}) I.domain A R ↔
      I.UniversalSound A R := Iff.rfl

theorem demotes_refl {α : Type*} (V : α → Set ℝ) (D : DomainBounds α) :
    Demotes V D V D := ⟨fun _ => ⟨id,id⟩,fun _ _ => Set.Subset.refl _⟩

theorem demotes_trans {α : Type*} {V U T : α → Set ℝ} {D E F : DomainBounds α}
    (h : Demotes V D U E) (k : Demotes U E T F) : Demotes V D T F := by
  refine ⟨fun p => ⟨fun hf => (h.1 p).1 ((k.1 p).1 hf),
    fun hd => (k.1 p).2 ((h.1 p).2 hd)⟩,?_⟩
  intro p hp
  exact (h.2 p hp).trans (k.2 p ((h.1 p).2 hp))

/-- General same-witness inclusion/demotion theorem. No success, totality,
attainment, representation algorithm or new numerical assumption is inferred. -/
theorem sound_demote {α W : Type*} {V U : α → Set ℝ} {D E : DomainBounds α}
    {A : α → W → Prop} {R : α → W → ℝ → Prop}
    (hs : Sound V D A R) (hd : Demotes V D U E) : Sound U E A R := by
  intro p w ha
  have h := hs p w ha
  exact ⟨fun z hz => hd.2 p (h.2.2 ⟨z,hz⟩) (h.1 z hz),
    DomainConstraints.weaken_compatible hd.1 h.2⟩

/-- A representation-changing model composition, independent of the concrete
source, intermediate and target representation types. -/
theorem model_demotion {α W X Y Z : Type*}
    (V : Y → α → Set ℝ) (D : Y → DomainBounds α)
    (U : Z → α → Set ℝ) (E : Z → DomainBounds α)
    (A : X → α → W → Prop) (R : X → α → W → ℝ → Prop)
    (model : X → Y) (demote : Y → Z)
    (hm : ∀ x, Sound (V (model x)) (D (model x)) (A x) (R x))
    (hd : ∀ y, Demotes (V y) (D y) (U (demote y)) (E (demote y))) :
    ∀ x, Sound (U (demote (model x))) (E (demote (model x))) (A x) (R x) :=
  fun x => sound_demote (hm x) (hd (model x))

/-- Actual outputs, not products of independently projected marginal images. -/
def outputs {α W : Type*} (A : α → W → Prop) (R : α → W → ℝ → Prop)
    (p : α) : Set ℝ := {z | ∃ w, A p w ∧ R p w z}

theorem exact_sound {α W : Type*} (A : α → W → Prop) (R : α → W → ℝ → Prop) :
    Sound (outputs A R) (exactInputDomain A R) A R := by
  intro p w ha
  exact ⟨fun z hz => ⟨w,ha,hz⟩,fun hd => hd.2 w ha,fun ⟨z,hz⟩ => ⟨w,z,ha,hz⟩⟩

/-- Sound outward hull projection with exact input-domain classification retained. -/
theorem exact_hull_sound {α W : Type*} (A : α → W → Prop) (R : α → W → ℝ → Prop) :
    Sound (fun p => ExtendedImageHull.hull (outputs A R p)) (exactInputDomain A R) A R :=
  sound_demote (exact_sound A R)
    ⟨fun _ => ⟨id,id⟩,fun _ _ => ExtendedImageHull.sound _⟩

/-- The existing finite affine-to-constant projection instantiates Demotes.
Its possible-domain guard keeps the required unit-parameter hypothesis. -/
theorem affine_to_constant (I : LinearInterval) :
    Demotes (fun t => {z | I.Contains t z})
      (DomainConstraints.exactDomain (fun t => t ∈ Set.Icc (0:ℝ) 1))
      (fun _ => {z | I.hull.Contains z})
      (DomainConstraints.exactDomain (fun t => t ∈ Set.Icc (0:ℝ) 1)) :=
  ⟨fun _ => ⟨id,id⟩,fun _ ht _ hz => linear_hull_encloses ht hz⟩

theorem affine_constant_sound {W : Type*} (I : LinearInterval)
    (A : ℝ → W → Prop) (R : ℝ → W → ℝ → Prop)
    (h : Sound (fun t => {z | I.Contains t z})
      (DomainConstraints.exactDomain (fun t => t ∈ Set.Icc (0:ℝ) 1)) A R) :
    Sound (fun _ => {z | I.hull.Contains z})
      (DomainConstraints.exactDomain (fun t => t ∈ Set.Icc (0:ℝ) 1)) A R :=
  sound_demote h (affine_to_constant I)

/-- Changing representation does not discard an external domain hole. -/
theorem restrict_sound {α W : Type*} {V : α → Set ℝ} {D : DomainBounds α}
    {A : α → W → Prop} {R : α → W → ℝ → Prop} (h : Sound V D A R)
    (P : α → Prop) :
    Sound V ((DomainConstraints.exactDomain P).inter D) A (fun p w z => P p ∧ R p w z) := by
  intro p w ha
  have hh := h p w ha
  exact ⟨fun z hz => hh.1 z hz.2,
    fun hd => let ⟨z,hz⟩ := hh.2.1 hd.2; ⟨z,hd.1,hz⟩,
    fun ⟨z,hp,hz⟩ => ⟨hp,hh.2.2 ⟨z,hz⟩⟩⟩

end GeneralizedIntervalArithmetic.GeneralFamilyDemotion
