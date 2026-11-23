import RoundedAddition
import HardwareAddition
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace GeneralizedIntervalArithmetic.ExactImageHull

/-- Least closed real hull, used below only for nonempty bounded output sets. -/
noncomputable def hull (S : Set ℝ) : Set ℝ := Set.Icc (sInf S) (sSup S)

theorem sound {S : Set ℝ} (hl : BddBelow S) (hu : BddAbove S) : S ⊆ hull S :=
  fun _ hz => ⟨csInf_le hl hz, le_csSup hu hz⟩

theorem ordered {S : Set ℝ} (hne : S.Nonempty) (hl : BddBelow S) (hu : BddAbove S) :
    sInf S ≤ sSup S := csInf_le_csSup hl hu hne

/-- Any closed interval enclosing the actual image also encloses its hull. -/
theorem least {S : Set ℝ} (hne : S.Nonempty) {l u : ℝ}
    (h : S ⊆ Set.Icc l u) : hull S ⊆ Set.Icc l u := by
  intro z hz
  exact ⟨(le_csInf hne (fun _ hx => (h hx).1)).trans hz.1,
    hz.2.trans (csSup_le hne (fun _ hx => (h hx).2))⟩

theorem enclosure_iff {S : Set ℝ} (hne : S.Nonempty)
    (hl : BddBelow S) (hu : BddAbove S) (l u : ℝ) :
    S ⊆ Set.Icc l u ↔ hull S ⊆ Set.Icc l u :=
  ⟨least hne, fun h => (sound hl hu).trans h⟩

/-- Refinement is inclusion of actual output sets, not independence of inputs. -/
theorem mono {S T : Set ℝ} (hne : S.Nonempty)
    (hl : BddBelow T) (hu : BddAbove T) (hst : S ⊆ T) : hull S ⊆ hull T := by
  intro z hz
  exact ⟨(csInf_le_csInf hl hne hst).trans hz.1,
    hz.2.trans (csSup_le_csSup hu hne hst)⟩

/-- Attainment is an EXTRA hypothesis, used for the concrete closed-interval sum. -/
theorem eq_of_attained {S : Set ℝ} {l u : ℝ}
    (hb : S ⊆ Set.Icc l u) (hl : l ∈ S) (hu : u ∈ S) : hull S = Set.Icc l u := by
  have hinf : sInf S = l := le_antisymm (csInf_le ⟨l,fun _ hx => (hb hx).1⟩ hl)
    (le_csInf ⟨l,hl⟩ (fun _ hx => (hb hx).1))
  have hsup : sSup S = u := le_antisymm (csSup_le ⟨l,hl⟩ (fun _ hx => (hb hx).2))
    (le_csSup ⟨u,fun _ hx => (hb hx).2⟩ hu)
  simp [hull,hinf,hsup]

/-- Actual outputs from one admissible input witness. Relations permit partial
or multivalued semantics without assigning values at undefined inputs. -/
def values {α : Type*} (D : Set α) (R : α → ℝ → Prop) : Set ℝ :=
  {z | ∃ a ∈ D, R a z}

theorem values_total {α : Type*} (D : Set α) (f : α → ℝ) :
    values D (fun a z => z = f a) = f '' D := by
  ext z
  constructor
  · rintro ⟨a,ha,rfl⟩; exact ⟨a,ha,rfl⟩
  · rintro ⟨a,ha,rfl⟩; exact ⟨a,ha,rfl⟩

theorem values_refine {α : Type*} {D E : Set α} {R Q : α → ℝ → Prop}
    (hd : D ⊆ E) (hr : ∀ a ∈ D, ∀ z, R a z → Q a z) : values D R ⊆ values E Q := by
  rintro z ⟨a,ha,hz⟩
  exact ⟨a,hd ha,hr a ha z hz⟩

/-- Independent operands are explicit here, not assumed by the generic hull. -/
def sums (I J : QInterval) : Set ℝ :=
  values {p : ℝ × ℝ | I.Contains p.1 ∧ J.Contains p.2} (fun p z => z = p.1+p.2)

theorem sums_enclosed (I J : QInterval) : sums I J ⊆ {z | (I.add J).Contains z} := by
  rintro z ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
  exact add_encloses hx hy

theorem sums_endpoints (I J : QInterval) :
    ((I.add J).lo:ℝ) ∈ sums I J ∧ ((I.add J).hi:ℝ) ∈ sums I J := by
  have hi : (I.lo:ℝ) ≤ I.hi := by exact_mod_cast I.ordered
  have hj : (J.lo:ℝ) ≤ J.hi := by exact_mod_cast J.ordered
  constructor
  · exact ⟨⟨I.lo,J.lo⟩,⟨⟨le_rfl,hi⟩,⟨le_rfl,hj⟩⟩,by simp [QInterval.add]⟩
  · exact ⟨⟨I.hi,J.hi⟩,⟨⟨hi,le_rfl⟩,⟨hj,le_rfl⟩⟩,by simp [QInterval.add]⟩

theorem add_exact (I J : QInterval) : hull (sums I J) = {z | (I.add J).Contains z} :=
  eq_of_attained (sums_enclosed I J) (sums_endpoints I J).1 (sums_endpoints I J).2

/-- Reuse existing local rounding-contract soundness; no tight-rounding claim. -/
theorem rounded_add_contains_hull (I J : QInterval) (down up : ℚ → ℚ)
    (hd : down (I.lo+J.lo) ≤ I.lo+J.lo) (hu : I.hi+J.hi ≤ up (I.hi+J.hi)) :
    hull (sums I J) ⊆ {z | (roundedAdd I J down up hd hu).Contains z} := by
  apply least ⟨_,(sums_endpoints I J).1⟩
  rintro z ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
  exact rounded_add_encloses I J down up hd hu hx hy

/-- A single finite decoded output interval enclosing all actual outputs encloses
their least hull. Decode uniqueness keeps the very same result interval. -/
theorem decoded_contains_hull {F : Type} {decode : F → Option ℝ}
    {S : Set ℝ} (hne : S.Nonempty) {O : HardwareAddition.Bounds F}
    (he : ∀ z ∈ S, HardwareAddition.Contains decode O z) :
    ∀ z ∈ hull S, HardwareAddition.Contains decode O z := by
  obtain ⟨v,hv⟩ := hne
  obtain ⟨l,u,hl,hu,_⟩ := he v hv
  have hb : S ⊆ Set.Icc l u := by
    intro z hz
    obtain ⟨l',u',hl',hu',hb⟩ := he z hz
    have el := Option.some.inj (hl'.symm.trans hl)
    have eu := Option.some.inj (hu'.symm.trans hu)
    subst l'; subst u'; exact hb
  intro z hz
  exact ⟨l,u,hl,hu,least ⟨v,hv⟩ hb hz⟩

/-- Observed hardware addition contracts discharge enclosure; this does not
promise success, native equivalence, or the least representable rounded hull. -/
theorem hardware_add_contains_hull {F : Type} {decode : F → Option ℝ}
    (I J : QInterval) {A B O : HardwareAddition.Bounds F}
    (ha0 : decode A.lo = some (I.lo:ℝ)) (ha1 : decode A.hi = some (I.hi:ℝ))
    (hb0 : decode B.lo = some (J.lo:ℝ)) (hb1 : decode B.hi = some (J.hi:ℝ))
    {lower upper : Option (F × F)}
    (hl : HardwareAddition.CallSound decode A.lo B.lo lower)
    (hu : HardwareAddition.CallSound decode A.hi B.hi upper)
    (hs : HardwareAddition.assemble lower upper = some O) :
    ∀ z ∈ hull (sums I J), HardwareAddition.Contains decode O z := by
  apply decoded_contains_hull ⟨_,(sums_endpoints I J).1⟩
  rintro z ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
  exact HardwareAddition.assemble_encloses hl hu hs
    ⟨_,_,ha0,ha1,hx⟩ ⟨_,_,hb0,hb1,hy⟩

end GeneralizedIntervalArithmetic.ExactImageHull
