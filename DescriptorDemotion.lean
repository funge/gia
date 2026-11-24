import NumberPromotion
import DomainConstraints

/-! Tupper §2.11.2–3: whole-set descriptor demotion and classification.
Infinite bounds enclose real descriptors; no literal exceptional arithmetic. -/
namespace GeneralizedIntervalArithmetic.DescriptorDemotion
open DomainConstraints

/-- Reuse the existing exact domain envelope. Empty fibers are not vacuously
true; P is the numerical descriptor interpretation, not numerical equality. -/
def domain {α X : Type*} (S : α → Set X) (P : X → Prop) : DomainBounds α :=
  exactInputDomain (fun p x => x ∈ S p) (fun _ x z => P x ∧ z=0)

theorem definite_iff {α X : Type*} (S : α → Set X) (P : X → Prop) (p : α) :
    (domain S P).definite p ↔ (S p).Nonempty ∧ ∀ x ∈ S p, P x := by
  simp [domain, exactInputDomain, Set.Nonempty]

theorem possible_iff {α X : Type*} (S : α → Set X) (P : X → Prop) (p : α) :
    (domain S P).possible p ↔ ∃ x ∈ S p, P x := by
  simp [domain, exactInputDomain, Set.Nonempty]

/-- Exact weakest additional condition for description refinement given set
inclusion, under this project's explicit empty-fiber convention. -/
theorem widen_refines_iff {α X : Type*} (S T : α → Set X) (P : X → Prop)
    (hs : ∀ p, S p ⊆ T p) :
    Refines (domain S P) (domain T P) ↔
      ∀ p, (T p).Nonempty → (∀ x ∈ T p, P x) → (S p).Nonempty := by
  constructor
  · intro h p hn hall
    exact ((definite_iff S P p).mp ((h p).1 ((definite_iff T P p).mpr ⟨hn,hall⟩))).1
  · intro h p
    constructor
    · intro hd
      obtain ⟨hn,hall⟩ := (definite_iff T P p).mp hd
      exact (definite_iff S P p).mpr ⟨h p hn hall,fun x hx => hall x (hs p hx)⟩
    · intro hp
      obtain ⟨x,hx,hp⟩ := (possible_iff S P p).mp hp
      exact (possible_iff T P p).mpr ⟨x,hs p hx,hp⟩

theorem integer_hull_nonempty (S : Set ℝ) : (NumberPromotion.hull S).Nonempty ↔ S.Nonempty := by
  constructor
  · intro hn
    by_contra hs
    have he := Set.not_nonempty_iff_eq_empty.mp hs
    simp [he, NumberPromotion.empty] at hn
  · rintro ⟨x,hx⟩
    exact ⟨x,NumberPromotion.sound S hx⟩

/-- Actual outward integer-endpoint conversion discharges the inclusion and
empty-fiber premises, for arbitrary real sets and arbitrary predicates. -/
theorem integer_hull_refines {α : Type*} (S : α → Set ℝ) (P : ℝ → Prop) :
    Refines (domain S P) (domain (fun p => NumberPromotion.hull (S p)) P) :=
  (widen_refines_iff _ _ P (fun p => NumberPromotion.sound (S p))).mpr
    (fun p hn _ => (integer_hull_nonempty (S p)).mp hn)

theorem witness_compatible {α X : Type*} (S : α → Set X) (P : X → Prop)
    (p : α) (x : X) (hx : x ∈ S p) : (domain S P).Compatible p (P x) :=
  ⟨fun hd => ((definite_iff S P p).mp hd).2 x hx,
    fun hp => (possible_iff S P p).mpr ⟨x,hx,hp⟩⟩

/-- Partial domain and descriptor value use one actual witness. Widening does
not replace x by its rounded endpoint or discard the external hole predicate. -/
theorem guarded_integer_compatible {α : Type*} (S : α → Set ℝ) (P : ℝ → Prop)
    (G : DomainBounds α) (p : α) (A : Prop) (x : ℝ)
    (hg : G.Compatible p A) (hx : A → x ∈ S p) :
    (G.inter (domain (fun p => NumberPromotion.hull (S p)) P)).Compatible p (A ∧ P x) := by
  constructor
  · rintro ⟨ha,hd⟩
    have hA := hg.1 ha
    exact ⟨hA,(witness_compatible _ P p x (NumberPromotion.sound _ (hx hA))).1 hd⟩
  · rintro ⟨ha,hp⟩
    exact ⟨hg.2 ha,(witness_compatible _ P p x (NumberPromotion.sound _ (hx ha))).2 hp⟩

/-- Inclusion alone cannot turn the empty descriptor fiber into definite truth. -/
theorem empty_widening_counterexample :
    (∅ : Set ℝ) ⊆ {0} ∧
    ¬ Refines (domain (fun _ : Unit => (∅ : Set ℝ)) (fun _ => True))
      (domain (fun _ : Unit => ({0} : Set ℝ)) (fun _ => True)) := by
  refine ⟨Set.empty_subset _, ?_⟩
  intro h
  have hd := (h ()).1 ((definite_iff _ _ ()).mpr ⟨⟨0,by simp⟩,by simp⟩)
  have he := ((definite_iff _ _ ()).mp hd).1
  simp at he

/-- Rounding a descriptor point is NOT whole-set outward conversion. -/
theorem point_rounding_counterexample :
    (1/2:ℝ) ≠ 0 ∧ (⌊(1/2:ℝ)⌋ : ℤ) = 0 := by norm_num

/-- Successful bound translations only. Dropping `none` is a lossy projection,
not a domain-preserving promotion of a tagged descriptor family. -/
def boundImage (S : Set ExceptionalComparisons.Value) : Set EReal :=
  {b | ∃ v ∈ S, ExceptionalComparisons.bound v = some b}

theorem bound_defined_iff (v : ExceptionalComparisons.Value) :
    (∃ b, ExceptionalComparisons.bound v = some b) ↔ v ≠ .undefined := by
  cases v <;> simp [ExceptionalComparisons.bound]

/-- Sound repair: retain the original tag-domain description beside the bound
projection. Compatibility is checked for the same actual tag, including lambda. -/
theorem retained_tag_domain {α : Type*} (S : α → Set ExceptionalComparisons.Value)
    (p : α) (v : ExceptionalComparisons.Value) (hv : v ∈ S p) :
    (domain S (fun v => v ≠ .undefined)).Compatible p
      (∃ b, ExceptionalComparisons.bound v = some b) := by
  have h := witness_compatible S (fun v => v ≠ .undefined) p v hv
  exact ⟨fun hd => (bound_defined_iff v).mpr (h.1 hd),
    fun hb => h.2 ((bound_defined_iff v).mp hb)⟩

/-- Removing lambda before classifying remaining bounds incorrectly promotes
mixed definedness to definite truth. No exceptional arithmetic is presumed. -/
theorem dropping_lambda_counterexample :
    ¬ Refines
      (domain (fun _ : Unit => ({.undefined, .finite 0} : Set ExceptionalComparisons.Value))
        (fun v => v ≠ .undefined))
      (domain (fun _ : Unit => boundImage ({.undefined, .finite 0} : Set ExceptionalComparisons.Value))
        (fun _ => True)) := by
  intro h
  have ht : (domain (fun _ : Unit => boundImage ({.undefined, .finite 0} : Set ExceptionalComparisons.Value))
      (fun _ => True)).definite () := by
    apply (definite_iff _ _ ()).mpr
    exact ⟨⟨0,.finite 0,by simp,rfl⟩,fun _ _ => trivial⟩
  have hs := (definite_iff _ _ ()).mp ((h ()).1 ht)
  exact hs.2 .undefined (by simp) rfl

end GeneralizedIntervalArithmetic.DescriptorDemotion
