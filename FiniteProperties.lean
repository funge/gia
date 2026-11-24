import PartialProperties
import SemanticContinuity
import Mathlib.Order.Filter.Finite

/-! Finite strict composition of actual partial real functions. This is a
proof-side denotation, not an evaluation-order or executable backend claim. -/
namespace GeneralizedIntervalArithmetic.FiniteProperties
open PartialProperties Filter
open scoped Topology

/-- A tuple exists only when every input supplies an actual value. -/
noncomputable def collect {n : ℕ} (f : Fin n → PartialReal) (x : ℝ) : Option (Fin n → ℝ) := by
  classical
  exact if h : ∀ i, ∃ y, f i x = some y then some (fun i => Classical.choose (h i)) else none

theorem collect_some {n : ℕ} (f : Fin n → PartialReal) (x : ℝ) (v : Fin n → ℝ) :
    collect f x = some v ↔ ∀ i, f i x = some (v i) := by
  classical
  unfold collect
  split_ifs with h
  · constructor
    · intro he
      have hv : (fun i => Classical.choose (h i)) = v := Option.some.inj he
      intro i
      rw [← hv]
      exact Classical.choose_spec (h i)
    · intro hv
      congr 1
      funext i
      exact Option.some.inj ((Classical.choose_spec (h i)).symm.trans (hv i))
  · simp only [ reduceCtorEq,false_iff]
    intro hv
    exact h (fun i => ⟨v i,hv i⟩)

noncomputable def composeN {n : ℕ} (g : (Fin n → ℝ) → Option ℝ)
    (f : Fin n → PartialReal) : PartialReal := fun x => (collect f x).bind g

theorem composeN_some {n : ℕ} (g : (Fin n → ℝ) → Option ℝ)
    (f : Fin n → PartialReal) (x z : ℝ) :
    composeN g f x = some z ↔ ∃ v, (∀ i, f i x = some (v i)) ∧ g v = some z := by
  have hb : composeN g f x = some z ↔ ∃ v, collect f x = some v ∧ g v = some z := by
    cases hc : collect f x <;> simp [composeN,hc]
  simpa only [collect_some] using hb

theorem composeN_defined {n : ℕ} (g : (Fin n → ℝ) → Option ℝ)
    (f : Fin n → PartialReal) (x : ℝ) :
    (∃ z, composeN g f x = some z) ↔
      ∃ v, (∀ i, f i x = some (v i)) ∧ ∃ z, g v = some z := by
  simp only [composeN_some]
  aesop

theorem missing_input {n : ℕ} (g : (Fin n → ℝ) → Option ℝ)
    (f : Fin n → PartialReal) (x : ℝ) (i : Fin n) (hi : f i x = none) :
    composeN g f x = none := by
  cases hc : composeN g f x with
  | none => rfl
  | some z =>
    obtain ⟨v,hv,_⟩ := (composeN_some g f x z).mp hc
    simpa [hi] using hv i

/-- Continuous real representative of the outer partial operation on its domain. -/
theorem continuous_composeN {n : ℕ} {g : (Fin n → ℝ) → Option ℝ}
    {f : Fin n → PartialReal} {S : Set ℝ} {T : Set (Fin n → ℝ)}
    (hf : ∀ i, ContinuousOnPartial (f i) S)
    (hg : ∃ b : (Fin n → ℝ) → ℝ, ContinuousOn b T ∧ ∀ v ∈ T, g v = some (b v))
    (hm : ∀ x ∈ S, ∀ v, (∀ i, f i x = some (v i)) → v ∈ T) :
    ContinuousOnPartial (composeN g f) S := by
  classical
  choose a ca ha using hf
  obtain ⟨b,cb,hb⟩ := hg
  have hc : ContinuousOn (fun x i => a i x) S := continuousOn_pi.mpr ca
  have maps : Set.MapsTo (fun x i => a i x) S T := fun x hx => hm x hx _ (fun i => ha i x hx)
  refine ⟨fun x => b (fun i => a i x),cb.comp hc maps,?_⟩
  intro x hx
  exact (composeN_some g f x _).mpr ⟨_,fun i => ha i x hx,hb _ (maps hx)⟩

/-- Actual local constancy relative to S, including definedness at the point.
An empty punctured domain does not remove the separate point-value premise. -/
def LocallyConstantWithin (f : PartialReal) (S : Set ℝ) (x : ℝ) : Prop :=
  ∃ z, f x = some z ∧ ∀ᶠ y in nhdsWithin x S, f y = some z

/-- Finitely many locally constant children give one common neighborhood.
The outer operation need only be defined on their fixed tuple. -/
theorem locally_constant_composeN {n : ℕ} {g : (Fin n → ℝ) → Option ℝ}
    {f : Fin n → PartialReal} {S : Set ℝ} {x : ℝ}
    (hf : ∀ i, LocallyConstantWithin (f i) S x)
    (hg : ∃ v z, (∀ i, f i x = some (v i)) ∧ g v = some z) :
    LocallyConstantWithin (composeN g f) S x := by
  classical
  obtain ⟨v,z,hv,hz⟩ := hg
  have he : ∀ i, ∀ᶠ y in nhdsWithin x S, f i y = some (v i) := by
    intro i
    obtain ⟨w,hw,hn⟩ := hf i
    have eqv : w = v i := Option.some.inj (hw.symm.trans (hv i))
    simpa [eqv] using hn
  refine ⟨z,(composeN_some g f x z).mpr ⟨v,hv,hz⟩,?_⟩
  exact (Filter.eventually_all.mpr he).mono (fun y hy =>
    (composeN_some g f y z).mpr ⟨v,hy,hz⟩)

/-- Existing recursive expression semantics: locally fixed coordinates retain
an actual value witness, including every original division guard. -/
theorem expr_locally_fixed {X Y : ℝ → ℝ} {S : Set ℝ} {x z : ℝ} (e : Expr)
    (hv : Value (X x) (Y x) e z)
    (hx : ∀ᶠ y in nhdsWithin x S, X y = X x)
    (hy : ∀ᶠ y in nhdsWithin x S, Y y = Y x) :
    ∀ᶠ y in nhdsWithin x S, Value (X y) (Y y) e z :=
  (hx.and hy).mono (fun _ h => by rw [h.1,h.2]; exact hv)

end GeneralizedIntervalArithmetic.FiniteProperties
