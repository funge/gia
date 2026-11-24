import DescriptorDemotion

/-! Derived representation rule for Tupper §§2.6, 2.9.1 and 2.11.
Real payload conversion and literal exceptional tags are separate. -/
namespace GeneralizedIntervalArithmetic.TaggedConversion
local notation "Tag" => ExceptionalComparisons.Value

def finitePart (S : Set Tag) : Set ℝ := {x | ExceptionalComparisons.Value.finite x ∈ S}

/-- Convert only the real payload family, retaining each exceptional tag exactly.
Infinite endpoints inside C are bounds, never automatically literal values. -/
def lift (C : Set ℝ → Set ℝ) (S : Set Tag) : Set Tag
  | .finite x => x ∈ C (finitePart S)
  | .negInf => .negInf ∈ S
  | .posInf => .posInf ∈ S
  | .undefined => .undefined ∈ S

theorem finitePart_lift (C : Set ℝ → Set ℝ) (S : Set Tag) :
    finitePart (lift C S) = C (finitePart S) := rfl

theorem exceptional_exact (C : Set ℝ → Set ℝ) (S : Set Tag) :
    (.negInf ∈ lift C S ↔ .negInf ∈ S) ∧
    (.posInf ∈ lift C S ↔ .posInf ∈ S) ∧
    (.undefined ∈ lift C S ↔ .undefined ∈ S) := ⟨Iff.rfl,Iff.rfl,Iff.rfl⟩

/-- Exact denotation of composition, even when C and D are lossy enclosures. -/
theorem lift_comp (C D : Set ℝ → Set ℝ) (S : Set Tag) :
    lift D (lift C S) = lift (D ∘ C) S := by
  ext v
  cases v <;> rfl

theorem lift_sound (C : Set ℝ → Set ℝ) (h : ∀ S, S ⊆ C S) (S : Set Tag) :
    S ⊆ lift C S := by
  intro v hv
  cases v with
  | finite x => exact h (finitePart S) hv
  | negInf => exact hv
  | posInf => exact hv
  | undefined => exact hv

theorem lift_empty (C : Set ℝ → Set ℝ) (h : C ∅ = ∅) : lift C ∅ = ∅ := by
  have hf : finitePart (∅ : Set Tag) = ∅ := rfl
  ext v
  cases v with
  | finite x =>
    change x ∈ C (finitePart ∅) ↔ False
    rw [hf,h]
    simp
  | negInf => exact Iff.rfl
  | posInf => exact Iff.rfl
  | undefined => exact Iff.rfl

theorem lift_nonempty (C : Set ℝ → Set ℝ) (hs : ∀ S, S ⊆ C S) (he : C ∅ = ∅)
    (S : Set Tag) : (lift C S).Nonempty ↔ S.Nonempty := by
  constructor
  · intro hn
    by_contra h
    have hz := Set.not_nonempty_iff_eq_empty.mp h
    rw [hz, lift_empty C he] at hn
    exact Set.not_nonempty_empty hn
  · rintro ⟨v,hv⟩
    exact ⟨v,lift_sound C hs S hv⟩

/-- One composition/preservation rule: exact tag-aware composition, sound
same-value inclusion, and classification refinement at every shared parameter.
No operation on an exceptional value is inferred from conversion. -/
theorem composition_preserves {α : Type*} (C D : Set ℝ → Set ℝ)
    (hc : ∀ S, S ⊆ C S) (hd : ∀ S, S ⊆ D S)
    (ec : C ∅ = ∅) (ed : D ∅ = ∅)
    (S : α → Set Tag) (P : Tag → Prop) :
    (∀ p, lift D (lift C (S p)) = lift (D ∘ C) (S p)) ∧
    (∀ p, S p ⊆ lift D (lift C (S p))) ∧
    DomainConstraints.Refines (DescriptorDemotion.domain S P)
      (DescriptorDemotion.domain (fun p => lift D (lift C (S p))) P) := by
  have hi : ∀ p, S p ⊆ lift D (lift C (S p)) :=
    fun p => (lift_sound C hc (S p)).trans (lift_sound D hd _)
  refine ⟨fun p => lift_comp C D (S p), hi, ?_⟩
  apply (DescriptorDemotion.widen_refines_iff _ _ P hi).mpr
  intro p hn _
  exact (lift_nonempty C hc ec _).mp ((lift_nonempty D hd ed _).mp hn)

/-- Retains the actual tag and an external domain guard; absence of an input
cannot become a value by converting its enclosing family. -/
theorem guarded_witness {α : Type*} (C D : Set ℝ → Set ℝ)
    (hc : ∀ S, S ⊆ C S) (hd : ∀ S, S ⊆ D S)
    (S : α → Set Tag) (P : Tag → Prop) (G : DomainBounds α)
    (p : α) (A : Prop) (v : Tag) (hg : G.Compatible p A) (hv : A → v ∈ S p) :
    (G.inter (DescriptorDemotion.domain (fun p => lift D (lift C (S p))) P)).Compatible p
      (A ∧ P v) := by
  have hw (ha : A) := DescriptorDemotion.witness_compatible
    (fun p => lift D (lift C (S p))) P p v
    (lift_sound D hd _ (lift_sound C hc _ (hv ha)))
  exact ⟨fun ⟨ha,hp⟩ => ⟨hg.1 ha,(hw (hg.1 ha)).1 hp⟩,
    fun ⟨ha,hp⟩ => ⟨hg.2 ha,(hw ha).2 hp⟩⟩

/-- Exact existence of a defined tag: finite widening cannot create one out of
an empty real payload family. This is not definedness of an unspecified operator. -/
theorem defined_exists (C : Set ℝ → Set ℝ) (hs : ∀ S, S ⊆ C S) (he : C ∅ = ∅)
    (S : Set Tag) :
    (∃ v ∈ lift C S, v ≠ .undefined) ↔ ∃ v ∈ S, v ≠ .undefined := by
  constructor
  · rintro ⟨v,hv,hdef⟩
    cases v with
    | finite x =>
      have hn : (finitePart S).Nonempty := by
        by_contra h
        have hz := Set.not_nonempty_iff_eq_empty.mp h
        change x ∈ C (finitePart S) at hv
        rw [hz,he] at hv
        exact hv
      obtain ⟨y,hy⟩ := hn
      exact ⟨.finite y,hy,by intro h; cases h⟩
    | negInf => exact ⟨.negInf,hv,by intro h; cases h⟩
    | posInf => exact ⟨.posInf,hv,by intro h; cases h⟩
    | undefined => exact (hdef rfl).elim
  · rintro ⟨v,hv,hd⟩
    exact ⟨v,lift_sound C hs S hv,hd⟩

/-- Exact lower/upper definedness bits, stronger than arbitrary-predicate
refinement. The original nonempty-fiber convention is retained. -/
theorem definedness_exact {α : Type*} (C : Set ℝ → Set ℝ)
    (hs : ∀ S, S ⊆ C S) (he : C ∅ = ∅) (S : α → Set Tag) (p : α) :
    ((DescriptorDemotion.domain (fun p => lift C (S p)) (fun v => v ≠ .undefined)).definite p ↔
      (DescriptorDemotion.domain S (fun v => v ≠ .undefined)).definite p) ∧
    ((DescriptorDemotion.domain (fun p => lift C (S p)) (fun v => v ≠ .undefined)).possible p ↔
      (DescriptorDemotion.domain S (fun v => v ≠ .undefined)).possible p) := by
  have hall : (∀ v ∈ lift C (S p), v ≠ .undefined) ↔ ∀ v ∈ S p, v ≠ .undefined := by
    constructor
    · intro h v hv
      exact h v (lift_sound C hs _ hv)
    · intro h v hv heq
      subst v
      exact h .undefined hv rfl
  simp only [DescriptorDemotion.definite_iff, DescriptorDemotion.possible_iff]
  exact ⟨and_congr (lift_nonempty C hs he _) hall,defined_exists C hs he _⟩

/-- Concrete two-stage real-hull then integer-endpoint-hull instance. -/
theorem hull_chain {α : Type*} (S : α → Set Tag) (P : Tag → Prop) :
    DomainConstraints.Refines (DescriptorDemotion.domain S P)
      (DescriptorDemotion.domain
        (fun p => lift NumberPromotion.hull (lift ExtendedImageHull.hull (S p))) P) :=
  (composition_preserves ExtendedImageHull.hull NumberPromotion.hull
    ExtendedImageHull.sound NumberPromotion.sound ExtendedImageHull.empty_hull
    NumberPromotion.empty S P).2.2

/-- A computable observation of representation categories, not source numerical equality. -/
inductive Kind where | finite | negInf | posInf | undefined deriving DecidableEq

def kind : Tag → Kind
  | .finite _ => .finite | .negInf => .negInf | .posInf => .posInf | .undefined => .undefined

def finiteOnly : Tag → Option ℝ
  | .finite x => some x | _ => none

def restoreFinite : Option ℝ → Tag
  | some x => .finite x | none => .undefined

/-- Decidable control: Option Real cannot retain the signed infinities as well
as lambda if every nonfinite case is encoded by the same none. -/
theorem finite_only_loss :
    kind (restoreFinite (finiteOnly .negInf)) ≠ kind .negInf ∧
    kind (restoreFinite (finiteOnly .posInf)) ≠ kind .posInf ∧
    kind (restoreFinite (finiteOnly .undefined)) = kind .undefined := by decide

end GeneralizedIntervalArithmetic.TaggedConversion
