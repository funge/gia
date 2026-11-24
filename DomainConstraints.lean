import BooleanComposition
import UniversalDomains
import AffineDomainGuards

/-! Tupper §2.11.4: conjunction at one shared parameter. Classification
weakening is semantic inclusion, not a numerical demotion algorithm. -/
namespace GeneralizedIntervalArithmetic.DomainConstraints
open StrictComparison BooleanComposition

/-- A domain description denotes allowed definedness Booleans, not necessarily
attained outcomes. This differs from exact independent comparison images. -/
noncomputable def description {α : Type*} (D : DomainBounds α) (p : α) : Truth := by
  classical
  exact if D.definite p then .trueOnly else if D.possible p then .both else .falseOnly

theorem description_compatible {α : Type*} (D : DomainBounds α) (p : α) (P : Prop) [Decidable P] :
    (decide P ∈ (description D p).values) ↔ D.Compatible p P := by
  classical
  have hc := D.consistent p
  unfold description
  split_ifs <;> simp_all [Truth.values, DomainBounds.Compatible]
  exact (em P).symm

theorem description_inter {α : Type*} (D E : DomainBounds α) (p : α) :
    description (D.inter E) p = conj (description D p) (description E p) := by
  classical
  have hd := D.consistent p
  have he := E.consistent p
  unfold description DomainBounds.inter
  split_ifs <;> simp_all [conj]

/-- A supplied exact predicate can be used without introducing another guard type. -/
def exactDomain {α : Type*} (P : α → Prop) : DomainBounds α := ⟨P, P, fun _ h => h⟩

/-- Reuse existing intersection; the empty family imposes no constraints. -/
def allDomains {α : Type*} (ds : List (DomainBounds α)) : DomainBounds α :=
  ds.foldr DomainBounds.inter (exactDomain (fun _ => True))

theorem all_definite {α : Type*} (ds : List (DomainBounds α)) (p : α) :
    (allDomains ds).definite p ↔ ∀ D ∈ ds, D.definite p := by
  induction ds with
  | nil => simp [allDomains, exactDomain]
  | cons D ds ih => simpa [allDomains, DomainBounds.inter] using
      (and_congr_right (fun _ => ih))

theorem all_possible {α : Type*} (ds : List (DomainBounds α)) (p : α) :
    (allDomains ds).possible p ↔ ∀ D ∈ ds, D.possible p := by
  induction ds with
  | nil => simp [allDomains, exactDomain]
  | cons D ds ih => simpa [allDomains, DomainBounds.inter] using
      (and_congr_right (fun _ => ih))

theorem all_description {α : Type*} (ds : List (DomainBounds α)) (p : α) :
    description (allDomains ds) p =
      (ds.map (fun D => description D p)).foldr conj .trueOnly := by
  induction ds with
  | nil => simp [allDomains, exactDomain, description]
  | cons D ds ih => simpa [allDomains] using
      (description_inter D (allDomains ds) p).trans (congrArg (conj (description D p)) ih)

/-- Finite lists implement constraint sets: order and repetitions do not affect
classification when membership agrees. -/
theorem all_description_ext {α : Type*} {ds es : List (DomainBounds α)}
    (h : ∀ D, D ∈ ds ↔ D ∈ es) (p : α) :
    description (allDomains ds) p = description (allDomains es) p := by
  classical
  have hd : (allDomains ds).definite p ↔ (allDomains es).definite p := by
    simp only [all_definite]
    exact ⟨fun hd D he => hd D ((h D).mpr he),
      fun he D hd => he D ((h D).mp hd)⟩
  have hp : (allDomains ds).possible p ↔ (allDomains es).possible p := by
    simp only [all_possible]
    exact ⟨fun hd D he => hd D ((h D).mpr he),
      fun he D hd => he D ((h D).mp hd)⟩
  simp only [description, propext hd, propext hp]

/-- Every constraint refers to the SAME p (and, when used universally, w). -/
theorem all_compatible {α ι : Type*} (ids : List ι) (D : ι → DomainBounds α)
    (C : ι → Prop) (p : α) (h : ∀ i ∈ ids, (D i).Compatible p (C i)) :
    (allDomains (ids.map D)).Compatible p (∀ i ∈ ids, C i) := by
  constructor
  · intro hd i hi
    exact (h i hi).1 ((all_definite _ _).mp hd (D i) (List.mem_map_of_mem hi))
  · intro hc
    rw [all_possible]
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    exact (h i hi).2 (hc i hi)

/-- Source's extra partial-operation guard is another constraint, at the same p. -/
theorem partial_guard_compatible {α ι : Type*} (ids : List ι)
    (D : ι → DomainBounds α) (C : ι → Prop) (G : DomainBounds α)
    (P : Prop) (p : α) (h : ∀ i ∈ ids, (D i).Compatible p (C i))
    (hg : G.Compatible p P) :
    (allDomains (G :: ids.map D)).Compatible p (P ∧ ∀ i ∈ ids, C i) := by
  have hc := all_compatible ids D C p h
  exact ⟨fun hd => ⟨hg.1 hd.1, hc.1 hd.2⟩,
    fun hp => ⟨hg.2 hp.1, hc.2 hp.2⟩⟩

/-- D is at least as informative as E, pointwise. -/
def Refines {α : Type*} (D E : DomainBounds α) : Prop :=
  ∀ p, (E.definite p → D.definite p) ∧ (D.possible p → E.possible p)

theorem refines_description {α : Type*} {D E : DomainBounds α} (h : Refines D E) (p : α) :
    (description D p).Refines (description E p) := by
  classical
  have hd := D.consistent p
  have he := E.consistent p
  have hh := h p
  rw [StrictComparison.refines_iff]
  unfold description
  split_ifs <;> simp_all

theorem all_refines {α ι : Type*} (ids : List ι) (D E : ι → DomainBounds α)
    (h : ∀ i ∈ ids, Refines (D i) (E i)) :
    Refines (allDomains (ids.map D)) (allDomains (ids.map E)) := by
  intro p
  constructor
  · intro he
    rw [all_definite] at he ⊢
    rintro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    exact (h i hi p).1 (he (E i) (List.mem_map_of_mem hi))
  · intro hd
    rw [all_possible] at hd ⊢
    rintro e he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    exact (h i hi p).2 (hd (D i) (List.mem_map_of_mem hi))

theorem weaken_compatible {α : Type*} {D E : DomainBounds α}
    (h : Refines D E) {p : α} {P : Prop} (hc : D.Compatible p P) : E.Compatible p P :=
  ⟨fun he => hc.1 ((h p).1 he), fun hp => (h p).2 (hc.2 hp)⟩

theorem weaken_universal {α W : Type*} {I : PartialEnclosure α} {E : DomainBounds α}
    {A : α → W → Prop} {R : α → W → ℝ → Prop}
    (h : I.UniversalSound A R) (hw : Refines I.domain E) :
    (PartialEnclosure.mk I.values E).UniversalSound A R := by
  intro p w ha
  exact ⟨(h p w ha).1, weaken_compatible hw (h p w ha).2⟩

/-- Source-to-existing-contract bridge. An operation's domain equivalence and
value enclosure must be proved; neither is inferred from possible constraints. -/
theorem constraints_universal {α W ι : Type*} (ids : List ι)
    (D : ι → DomainBounds α) (C : ι → α → W → Prop)
    (A : α → W → Prop) (R : α → W → ℝ → Prop) (V : FunctionalBounds α)
    (hc : ∀ p w, A p w → ∀ i ∈ ids, (D i).Compatible p (C i p w))
    (hd : ∀ p w, A p w → ((∃ z, R p w z) ↔ ∀ i ∈ ids, C i p w))
    (hv : ∀ p w, A p w → ∀ z, R p w z → V.Contains p z) :
    (PartialEnclosure.mk V (allDomains (ids.map D))).UniversalSound A R := by
  intro p w ha
  have h := all_compatible ids D (fun i => C i p w) p (hc p w ha)
  exact ⟨hv p w ha, fun hp => (hd p w ha).mpr (h.1 hp),
    fun hz => h.2 ((hd p w ha).mp hz)⟩

/-- Existing exact expression-domain theorem supplies a concrete model instance.
No bounded reciprocal range or independence of coordinate witnesses is assumed. -/
theorem reciprocal_constraints (gs : List RationalAffineForm) (p : ℝ × ℝ) :
    (allDomains (gs.map (fun a => exactDomain (fun q => a.value q ≠ 0)))).Compatible p
      (∃ z, Value p.1 p.2 (affineReciprocalSum gs) z) := by
  have h := all_compatible gs (fun a => exactDomain (fun q => a.value q ≠ 0))
    (fun a => a.value p ≠ 0) p (fun _ _ => ⟨id, id⟩)
  rw [affine_sum_defined_iff]
  exact h

end GeneralizedIntervalArithmetic.DomainConstraints
