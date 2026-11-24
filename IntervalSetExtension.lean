import IntervalSetDenotation
import GeneralFamilyDemotion

/-! General §2.13 set extension at one shared parameter. Relations retain partiality. -/
namespace GeneralizedIntervalArithmetic.IntervalSetExtension
open IntervalSetDenotation GeneralFamilyDemotion
open scoped BigOperators

variable {P Y : Type*} {m : ℕ}

/-- Each coordinate chooses its own piece, but all are evaluated at the SAME p. -/
def Choices (J : Fin m → Set Y) : Set (Fin m → Y) := {j|∀ i,j i ∈ J i}

theorem extension_exact (V : Y → P → Set ℝ) (J : Fin m → Set Y)
    (G : P → (Fin m → ℝ) → ℝ → Prop) (p : P) :
    denote (fun j => outputs (fun p x=>∀ i,x i ∈ V (j i) p) G) (Choices J) p =
      outputs (fun p x=>∀ i,x i ∈ denote V (J i) p) G p := by
  ext z
  constructor
  · rintro ⟨j,hj,x,hx,hg⟩
    exact ⟨x,fun i=>⟨j i,hj i,hx i⟩,hg⟩
  · rintro ⟨x,hx,hg⟩
    choose j hj hv using hx
    exact ⟨j,hj,x,hv,hg⟩

/-- Sound piece models lift to a sound union; the chosen tuple and p survive. -/
theorem lift_encloses (V : Y → P → Set ℝ) (J : Fin m → Set Y)
    (G : P → (Fin m → ℝ) → ℝ → Prop) (M : (Fin m → Y) → P → Set ℝ)
    (hm : ∀ j ∈ Choices J, ∀ p, outputs (fun p x=>∀ i,x i ∈ V (j i) p) G p ⊆ M j p)
    (p : P) :
    outputs (fun p x=>∀ i,x i ∈ denote V (J i) p) G p ⊆ denote M (Choices J) p := by
  rw [← extension_exact]
  rintro z ⟨j,hj,hz⟩
  exact ⟨j,hj,hm j hj p hz⟩

theorem lift_exact (V : Y → P → Set ℝ) (J : Fin m → Set Y)
    (G : P → (Fin m → ℝ) → ℝ → Prop) (M : (Fin m → Y) → P → Set ℝ)
    (hm : ∀ j ∈ Choices J, ∀ p, M j p = outputs (fun p x=>∀ i,x i ∈ V (j i) p) G p)
    (p : P) :
    denote M (Choices J) p = outputs (fun p x=>∀ i,x i ∈ denote V (J i) p) G p := by
  rw [← extension_exact]
  ext z
  constructor <;> rintro ⟨j,hj,hz⟩ <;> refine ⟨j,hj,?_⟩
  · simpa [hm j hj p] using hz
  · simpa [hm j hj p] using hz

/-- Same operator relation, smaller admitted input family: refinement is sound
without assuming endpoint attainability, nonempty images, or totality. -/
theorem extension_mono (V : Y → P → Set ℝ) (J K : Fin m → Set Y)
    (h : ∀ i,J i ⊆ K i) (G : P → (Fin m → ℝ) → ℝ → Prop) (p : P) :
    outputs (fun p x=>∀ i,x i ∈ denote V (J i) p) G p ⊆
      outputs (fun p x=>∀ i,x i ∈ denote V (K i) p) G p := by
  rintro z ⟨x,hx,hg⟩
  refine ⟨x,?_,hg⟩
  intro i
  obtain ⟨j,hj,hv⟩ := hx i
  exact ⟨j,h i hj,hv⟩

/-- A correlated input relation can use the lifted enclosure, but cannot infer
that independently admitted combinations are attainable. -/
theorem correlated_sound (V : Y → P → Set ℝ) (J : Fin m → Set Y)
    (G : P → (Fin m → ℝ) → ℝ → Prop) (A : P → (Fin m → ℝ) → Prop)
    (M : (Fin m → Y) → P → Set ℝ)
    (ha : ∀ p x, A p x → ∀ i,x i ∈ denote V (J i) p)
    (hm : ∀ j ∈ Choices J, ∀ p, outputs (fun p x=>∀ i,x i ∈ V (j i) p) G p ⊆ M j p) :
    Sound (fun p=>denote M (Choices J) p) (exactInputDomain A G) A G := by
  intro p x hx
  have hs := exact_sound A G p x hx
  refine ⟨?_,hs.2⟩
  intro z hz
  exact lift_encloses V J G M hm p ⟨x,ha p x hx,hz⟩

/-- The source's numerical equality guard, including the zero-dimensional case. -/
theorem squared_guard_iff {n : ℕ} (p q : Fin n → ℝ) :
    (∑ i,(p i-q i)^2) ≤ 0 ↔ p=q := by
  constructor
  · intro h
    apply funext
    intro i
    have hs : (p i-q i)^2 ≤ ∑ j,(p j-q j)^2 :=
      Finset.single_le_sum (fun j _=>sq_nonneg (p j-q j)) (Finset.mem_univ i)
    nlinarith [sq_nonneg (p i-q i)]
  · rintro rfl
    simp

/-- The point descriptions in the printed perfect-demotion construction.
D can be the unit cube or any common parameter domain. -/
def guardedPoint {n : ℕ} (g : (Fin n → ℝ) → Option ℝ)
    (q p : Fin n → ℝ) : Set ℝ :=
  {z | (∑ i,(p i-q i)^2) ≤ 0 ∧ g q = some z}

theorem guarded_points_exact {n : ℕ} (D : Set (Fin n → ℝ))
    (g : (Fin n → ℝ) → Option ℝ) (p : Fin n → ℝ) :
    denote (guardedPoint g) {q|q∈D ∧ ∃z,g q=some z} p = {z|p∈D ∧ g p=some z} := by
  ext z
  constructor
  · rintro ⟨q,⟨hq,hd⟩,hguard,hz⟩
    have he := (squared_guard_iff p q).mp hguard
    subst q
    exact ⟨hq,hz⟩
  · rintro ⟨hp,hz⟩
    exact ⟨p,⟨hp,z,hz⟩,(squared_guard_iff p p).mpr rfl,hz⟩

theorem guarded_point_correspondence {n : ℕ}
    (g : (Fin n → ℝ) → Option ℝ) (q p : Fin n → ℝ) :
    guardedPoint g q p = point g q p := by
  ext z
  simp [guardedPoint,point,squared_guard_iff]

/-- Quantified gap criterion: every closed interval enclosing the actual set
is strictly worse than that set, not just one selected loose model. -/
theorem strict_against_every_interval (S : Set ℝ) {a b c : ℝ}
    (ha : a∈S) (hb : b∈S) (hac : a≤c) (hcb : c≤b) (hc : c∉S) :
    ∀ l u : EReal, S ⊆ ExtendedImageHull.interval l u →
      S ⊂ ExtendedImageHull.interval l u := by
  intro l u h
  refine ⟨h,?_⟩
  intro hr
  apply hc
  apply hr
  exact ⟨(h ha).1.trans (by exact_mod_cast hac),
    (show (c:EReal) ≤ (b:EReal) by exact_mod_cast hcb).trans (h hb).2⟩

end GeneralizedIntervalArithmetic.IntervalSetExtension
