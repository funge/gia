import GeneralFamilyDemotion
import Mathlib.Topology.ContinuousOn

/-! Partial real-function core for §2.12. Filling a hole changes the function;
interval enclosure extension does not supply an expression value at that hole. -/
namespace GeneralizedIntervalArithmetic.PartialProperties

abbrev PartialReal := ℝ → Option ℝ

def Extends (f g : PartialReal) : Prop := ∀ x z, f x = some z → g x = some z

noncomputable def restrict (f : PartialReal) (S : Set ℝ) : PartialReal := by
  classical
  exact fun x => if x ∈ S then f x else none

def compose (g f : PartialReal) : PartialReal := fun x => (f x).bind g

theorem restrict_some (f : PartialReal) (S : Set ℝ) (x z : ℝ) :
    restrict f S x = some z ↔ x ∈ S ∧ f x = some z := by
  classical
  simp only [restrict]
  split_ifs <;> simp_all

theorem restrict_extends (f : PartialReal) (S : Set ℝ) : Extends (restrict f S) f :=
  fun x z hz => ((restrict_some f S x z).mp hz).2

theorem extends_trans {f g h : PartialReal} (hfg : Extends f g) (hgh : Extends g h) :
    Extends f h := fun x z hz => hgh x z (hfg x z hz)

/-- Exact strong definedness rule for strict unary composition, at one input. -/
theorem compose_some (g f : PartialReal) (x z : ℝ) :
    compose g f x = some z ↔ ∃ y, f x = some y ∧ g y = some z := by
  cases hf : f x <;> simp [compose,hf]

theorem compose_defined (g f : PartialReal) (x : ℝ) :
    (∃ z, compose g f x = some z) ↔ ∃ y, f x = some y ∧ ∃ z, g y = some z := by
  simp only [compose_some]
  aesop

/-- A defined continuous representative on S, using real topology, not a
chosen topology on Option. It asserts actual definedness at every point of S. -/
def ContinuousOnPartial (f : PartialReal) (S : Set ℝ) : Prop :=
  ∃ h : ℝ → ℝ, ContinuousOn h S ∧ ∀ x ∈ S, f x = some (h x)

theorem continuous_restrict {f : PartialReal} {S T : Set ℝ}
    (h : ContinuousOnPartial f S) (ht : T ⊆ S) : ContinuousOnPartial (restrict f T) T := by
  obtain ⟨g,hg,hv⟩ := h
  exact ⟨g,hg.mono ht,fun x hx => (restrict_some f T x (g x)).mpr ⟨hx,hv x (ht hx)⟩⟩

/-- Sufficient continuity composition, not the source's disputed reverse arrow. -/
theorem continuous_compose {f g : PartialReal} {S T : Set ℝ}
    (hf : ContinuousOnPartial f S) (hg : ContinuousOnPartial g T)
    (maps : ∀ x ∈ S, ∀ y, f x = some y → y ∈ T) :
    ContinuousOnPartial (compose g f) S := by
  obtain ⟨a,ca,ha⟩ := hf
  obtain ⟨b,cb,hb⟩ := hg
  have hm : Set.MapsTo a S T := fun x hx => maps x hx (a x) (ha x hx)
  refine ⟨b ∘ a,cb.comp ca hm,?_⟩
  intro x hx
  exact (compose_some g f x (b (a x))).mpr ⟨a x,ha x hx,hb _ (hm hx)⟩

/-- Bounds for an extension enclose the old function's values. Domain
classification is recomputed for the OLD function, never copied from the extension. -/
theorem extension_bounds_original {α W : Type*} (f g : PartialReal)
    (he : Extends f g) (input : α → W → ℝ) (A : α → W → Prop)
    (V : α → Set ℝ) (D : DomainBounds α)
    (hg : GeneralFamilyDemotion.Sound V D A (fun p w z => g (input p w) = some z)) :
    GeneralFamilyDemotion.Sound V
      (exactInputDomain A (fun p w z => f (input p w) = some z)) A
      (fun p w z => f (input p w) = some z) := by
  have hx := GeneralFamilyDemotion.exact_sound A (fun p w z => f (input p w) = some z)
  intro p w ha
  exact ⟨fun z hz => (hg p w ha).1 z (he _ _ hz),(hx p w ha).2⟩

/-- Property descriptions allow outcomes; they do not assert both are attained. -/
def Tracks {α W : Type*} (Q : DomainBounds α) (A : α → W → Prop)
    (P : α → W → Prop) : Prop := ∀ p w, A p w → Q.Compatible p (P p w)

theorem tracks_weaken {α W : Type*} {Q Q' : DomainBounds α}
    {A : α → W → Prop} {P : α → W → Prop}
    (h : Tracks Q A P) (hr : DomainConstraints.Refines Q Q') : Tracks Q' A P :=
  fun p w ha => DomainConstraints.weaken_compatible hr (h p w ha)

/-- Value/domain demotion and property demotion require their own proofs.
No property is inferred from numerical enclosure or recursive syntax alone. -/
theorem tracked_demotion {α W : Type*} {V U : α → Set ℝ} {D E Q Q' : DomainBounds α}
    {A : α → W → Prop} {R : α → W → ℝ → Prop} {P : α → W → Prop}
    (hs : GeneralFamilyDemotion.Sound V D A R) (hp : Tracks Q A P)
    (hv : GeneralFamilyDemotion.Demotes V D U E) (hq : DomainConstraints.Refines Q Q') :
    GeneralFamilyDemotion.Sound U E A R ∧ Tracks Q' A P :=
  ⟨GeneralFamilyDemotion.sound_demote hs hv,tracks_weaken hp hq⟩

end GeneralizedIntervalArithmetic.PartialProperties
