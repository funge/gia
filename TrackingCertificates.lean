import FiniteProperties

/-! A sufficient tracking rule, not a silent reversal of Tupper's printed
weak arrow. Exact strict-domain closure is proved separately. -/
namespace GeneralizedIntervalArithmetic.TrackingCertificates
open PartialProperties FiniteProperties DomainConstraints

/-- For a sufficient certificate, retain definite success only. Failure of
the certificate supplies no upper exclusion for the semantic property. -/
def sufficient {α : Type*} (Q : DomainBounds α) : DomainBounds α :=
  ⟨Q.definite, fun _ => True, fun _ _ => trivial⟩

theorem sufficient_compatible {α : Type*} {Q : DomainBounds α} {p : α}
    {C P : Prop} (hc : Q.Compatible p C) (h : C → P) :
    (sufficient Q).Compatible p P := ⟨fun hd => h (hc.1 hd), fun _ => trivial⟩

theorem sufficient_tracks {α W : Type*} {Q : DomainBounds α}
    {A C P : α → W → Prop} (hc : Tracks Q A C)
    (h : ∀ p w, A p w → C p w → P p w) : Tracks (sufficient Q) A P :=
  fun p w ha => sufficient_compatible (hc p w ha) (h p w ha)

/-- Concrete finite-arity continuity application. The supplied outer domain
and same-tuple mapping hypotheses remain essential. This is sufficient only. -/
theorem continuous_description {α : Type*} {n : ℕ}
    {g : (Fin n → ℝ) → Option ℝ} {f : Fin n → PartialReal}
    {S : Set ℝ} {T : Set (Fin n → ℝ)} {Q : DomainBounds α} {p : α}
    (hc : Q.Compatible p (∀ i, ContinuousOnPartial (f i) S))
    (hg : ∃ b : (Fin n → ℝ) → ℝ, ContinuousOn b T ∧ ∀ v ∈ T, g v = some (b v))
    (hm : ∀ x ∈ S, ∀ v, (∀ i, f i x = some (v i)) → v ∈ T) :
    (sufficient Q).Compatible p (ContinuousOnPartial (composeN g f) S) :=
  sufficient_compatible hc (fun hf => continuous_composeN hf hg hm)

/-- Universal guard on the actual child tuple. It is vacuous when a child is
absent; the separate conjunction of child definedness must not be dropped. -/
def OuterDefined {n : ℕ} (g : (Fin n → ℝ) → Option ℝ)
    (f : Fin n → PartialReal) (x : ℝ) : Prop :=
  ∀ v, (∀ i, f i x = some (v i)) → ∃ z, g v = some z

theorem defined_factorization {n : ℕ} (g : (Fin n → ℝ) → Option ℝ)
    (f : Fin n → PartialReal) (x : ℝ) :
    (∃ z, composeN g f x = some z) ↔
      (∀ i, ∃ y, f i x = some y) ∧ OuterDefined g f x := by
  classical
  rw [composeN_defined]
  constructor
  · rintro ⟨v, hv, hz⟩
    refine ⟨fun i => ⟨v i, hv i⟩, ?_⟩
    intro u hu
    have he : u = v := funext (fun i => Option.some.inj ((hu i).symm.trans (hv i)))
    simpa [he] using hz
  · rintro ⟨hf, hg⟩
    choose v hv using hf
    exact ⟨v, hv, hg v hv⟩

/-- Independent of the continuity interpretation: exact strict definedness
composes existing domain descriptions at the same parameter and input. -/
theorem defined_description {α : Type*} {n : ℕ}
    (g : (Fin n → ℝ) → Option ℝ) (f : Fin n → PartialReal) (x : ℝ)
    (D : Fin n → DomainBounds α) (G : DomainBounds α) (p : α)
    (hd : ∀ i, (D i).Compatible p (∃ y, f i x = some y))
    (hg : G.Compatible p (OuterDefined g f x)) :
    (allDomains (G :: (List.finRange n).map D)).Compatible p
      (∃ z, composeN g f x = some z) := by
  have hh := partial_guard_compatible (List.finRange n) D
    (fun i => ∃ y, f i x = some y) G (OuterDefined g f x) p
    (fun i _ => hd i) hg
  simp only [List.mem_finRange, forall_true_left] at hh
  exact ⟨fun h => (defined_factorization g f x).mpr ⟨(hh.1 h).2, (hh.1 h).1⟩,
    fun h => hh.2 ⟨((defined_factorization g f x).mp h).2,
      ((defined_factorization g f x).mp h).1⟩⟩

theorem no_possible_copy :
    (exactDomain (fun _ : Unit => False)).Compatible () False ∧
    ¬ (exactDomain (fun _ : Unit => False)).Compatible () True ∧
    (sufficient (exactDomain (fun _ : Unit => False))).Compatible () True := by
  exact ⟨⟨id, id⟩, fun h => h.2 trivial, ⟨False.elim, fun _ => trivial⟩⟩

open Filter
open scoped Topology

/-- Source-shaped coordinate freezing, on actual defined outer values.
This is a neighborhood certificate, not the printed weak implication. -/
def FrozenConstant {n : ℕ} (g : (Fin n → ℝ) → Option ℝ)
    (v : Fin n → ℝ) (B : Fin n → Prop) (z : ℝ) : Prop :=
  ∀ᶠ w in nhds v, (∀ i, B i → w i = v i) → g w = some z

/-- Sufficient local constancy from a common approaching tuple and flagged
fixed coordinates. Actual child values at the point and nearby are separate
premises: neither limits nor frozen coordinates create values at holes. -/
theorem frozen_composeN {n : ℕ} {g : (Fin n → ℝ) → Option ℝ}
    {f : Fin n → PartialReal} {S : Set ℝ} {x z : ℝ}
    {a : ℝ → Fin n → ℝ} {v : Fin n → ℝ} {B : Fin n → Prop}
    (hv : ∀ i, f i x = some (v i)) (hg : g v = some z)
    (ha : ∀ᶠ y in nhdsWithin x S, ∀ i, f i y = some (a y i))
    (ht : Tendsto a (nhdsWithin x S) (nhds v))
    (hf : ∀ i, B i → ∀ᶠ y in nhdsWithin x S, a y i = v i)
    (hc : FrozenConstant g v B z) :
    LocallyConstantWithin (composeN g f) S x := by
  have fixed : ∀ᶠ y in nhdsWithin x S, ∀ i, B i → a y i = v i :=
    Filter.eventually_all.mpr (fun i => by
      by_cases h : B i
      · exact (hf i h).mono (fun _ he _ => he)
      · exact Filter.Eventually.of_forall (fun _ hb => (h hb).elim))
  refine ⟨z, (composeN_some g f x z).mpr ⟨v, hv, hg⟩, ?_⟩
  exact ((ha.and fixed).and (ht hc)).mono (fun y h =>
    (composeN_some g f y z).mpr ⟨a y, h.1.1, h.2 h.1.2⟩)

end GeneralizedIntervalArithmetic.TrackingCertificates
