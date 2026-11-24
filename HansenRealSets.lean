import HansenCoefficients
import TaggedConversion
import GeneralFamilyDemotion

/-! Derived finite-real coefficient-set extension of the finite §2.14 model.
Infinite bounds are not coefficient values. Empty coefficients remain strict. -/
namespace GeneralizedIntervalArithmetic.HansenRealSets
open scoped BigOperators
open HansenCoefficients

def admissible {n} (P : Set ℝ) (Q : Fin n → Set ℝ) (w : Choice n) : Prop :=
  w.1 ∈ P ∧ ∀ i, w.2 i ∈ Q i
def values {n} (P : Set ℝ) (Q : Fin n → Set ℝ) (t : Fin n → ℝ) : Set ℝ :=
  {z | ∃ w, admissible P Q w ∧ z = value w t}

theorem nonempty_iff {n} (P : Set ℝ) (Q : Fin n → Set ℝ) (t : Fin n → ℝ) :
    (values P Q t).Nonempty ↔ P.Nonempty ∧ ∀ i, (Q i).Nonempty := by
  constructor
  · rintro ⟨z,w,hw,_⟩
    exact ⟨⟨w.1,hw.1⟩,fun i => ⟨w.2 i,hw.2 i⟩⟩
  · rintro ⟨⟨p,hp⟩,hq⟩
    choose q hq using hq
    exact ⟨value (p,q) t,(p,q),⟨hp,hq⟩,rfl⟩

theorem empty_coefficient {n} (P : Set ℝ) (Q : Fin n → Set ℝ) (t : Fin n → ℝ)
    (i : Fin n) (h : Q i = ∅) : values P Q t = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  rintro z ⟨w,hw,_⟩
  simpa [h] using hw.2 i

theorem zero_weights {n} (P : Set ℝ) (Q : Fin n → Set ℝ)
    (h : ∀ i, (Q i).Nonempty) : values P Q (fun _ => 0) = P := by
  choose q hq using h
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    simpa [value] using hw.1
  · intro hz
    exact ⟨(z,q),⟨hz,hq⟩,by simp [value]⟩

theorem finite_agreement {n} (P : QInterval) (Q : Fin n → QInterval) (t : Fin n → ℝ) :
    values {x | P.Contains x} (fun i => {x | (Q i).Contains x}) t =
      Set.Icc (HansenCoefficients.lower P Q t) (HansenCoefficients.upper P Q t) :=
  HansenCoefficients.exact_interval P Q t

theorem value_mix {n} (a b : Choice n) (s : ℝ) (t : Fin n → ℝ) :
    value (mix a b s) t = (1-s)*value a t+s*value b t := by
  simp only [value,mix]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem mix_admissible {n} {P : Set ℝ} {Q : Fin n → Set ℝ}
    (hp : Convex ℝ P) (hq : ∀ i, Convex ℝ (Q i)) {a b : Choice n}
    (ha : admissible P Q a) (hb : admissible P Q b) {s : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) 1) : admissible P Q (mix a b s) := by
  exact ⟨hp ha.1 hb.1 (sub_nonneg.mpr hs.2) hs.1 (by ring),
    fun i => hq i (ha.2 i) (hb.2 i) (sub_nonneg.mpr hs.2) hs.1 (by ring)⟩

/-- Every point between two attained values is attained, without boundedness or
closedness of any coefficient set. -/
theorem between {n} {P : Set ℝ} {Q : Fin n → Set ℝ}
    (hp : Convex ℝ P) (hq : ∀ i, Convex ℝ (Q i)) (t : Fin n → ℝ)
    {a b z : ℝ} (ha : a ∈ values P Q t) (hb : b ∈ values P Q t)
    (hz : z ∈ Set.Icc a b) : z ∈ values P Q t := by
  obtain ⟨u,hu,rfl⟩ := ha
  obtain ⟨v,hv,rfl⟩ := hb
  let f : ℝ → ℝ := fun s => value (mix u v s) t
  have hf : ContinuousOn f (Set.Icc 0 1) := by
    dsimp [f,value,mix]; fun_prop
  have h0 : f 0 = value u t := by simp [f,value,mix]
  have h1 : f 1 = value v t := by simp [f,value,mix]
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hf
    (show z ∈ Set.Icc (f 0) (f 1) by simpa [h0,h1] using hz)
  exact ⟨mix u v s,mix_admissible hp hq hu hv hs,he.symm⟩

/-- Strictly interior finite points of the extended least hull are actual values.
The boundary is not asserted attained. -/
theorem interior_attained {n} {P : Set ℝ} {Q : Fin n → Set ℝ}
    (hp : Convex ℝ P) (hq : ∀ i, Convex ℝ (Q i)) (t : Fin n → ℝ) {z : ℝ}
    (hl : ExtendedImageHull.lower (values P Q t) < (z : EReal))
    (hu : (z : EReal) < ExtendedImageHull.upper (values P Q t)) : z ∈ values P Q t := by
  have below : ∃ a ∈ values P Q t, a < z := by
    by_contra h
    push_neg at h
    have he : (z : EReal) ≤ ExtendedImageHull.lower (values P Q t) := by
      apply le_sInf
      rintro _ ⟨a,ha,rfl⟩
      exact EReal.coe_le_coe_iff.mpr (h a ha)
    exact (not_le_of_gt hl) he
  have above : ∃ b ∈ values P Q t, z < b := by
    by_contra h
    push_neg at h
    have he : ExtendedImageHull.upper (values P Q t) ≤ (z : EReal) := by
      apply sSup_le
      rintro _ ⟨b,hb,rfl⟩
      exact EReal.coe_le_coe_iff.mpr (h b hb)
    exact (not_le_of_gt hu) he
  obtain ⟨a,ha,haz⟩ := below
  obtain ⟨b,hb,hzb⟩ := above
  exact between hp hq t ha hb ⟨haz.le,hzb.le⟩

/-- Exact membership: open extended interior plus precisely the attained finite
boundary values. Infinite bounds are never real output witnesses. -/
theorem exact_membership {n} {P : Set ℝ} {Q : Fin n → Set ℝ}
    (hp : Convex ℝ P) (hq : ∀ i, Convex ℝ (Q i)) (t : Fin n → ℝ) (z : ℝ) :
    z ∈ values P Q t ↔
      (ExtendedImageHull.lower (values P Q t) < (z : EReal) ∧
       (z : EReal) < ExtendedImageHull.upper (values P Q t)) ∨
      (∃ w, admissible P Q w ∧ z = value w t ∧
        ((z : EReal) = ExtendedImageHull.lower (values P Q t) ∨
         (z : EReal) = ExtendedImageHull.upper (values P Q t))) := by
  constructor
  · intro hz
    have h := ExtendedImageHull.sound _ hz
    by_cases hl : ExtendedImageHull.lower (values P Q t) < (z : EReal)
    · by_cases hu : (z : EReal) < ExtendedImageHull.upper (values P Q t)
      · exact Or.inl ⟨hl,hu⟩
      · obtain ⟨w,hw,he⟩ := hz
        exact Or.inr ⟨w,hw,he,Or.inr (le_antisymm h.2 (le_of_not_gt hu))⟩
    · obtain ⟨w,hw,he⟩ := hz
      exact Or.inr ⟨w,hw,he,Or.inl (le_antisymm (le_of_not_gt hl) h.1)⟩
  · rintro (⟨hl,hu⟩ | ⟨w,hw,he,_⟩)
    · exact interior_attained hp hq t hl hu
    · exact ⟨w,hw,he⟩

/-- Closing the output loses nothing exactly when every finite boundary point
of the hull is attained. This also handles empty images and infinite bounds. -/
theorem hull_exact_iff {n} {P : Set ℝ} {Q : Fin n → Set ℝ}
    (hp : Convex ℝ P) (hq : ∀ i, Convex ℝ (Q i)) (t : Fin n → ℝ) :
    ExtendedImageHull.hull (values P Q t) = values P Q t ↔
    ∀ z ∈ ExtendedImageHull.hull (values P Q t),
      ((z : EReal) = ExtendedImageHull.lower (values P Q t) ∨
       (z : EReal) = ExtendedImageHull.upper (values P Q t)) → z ∈ values P Q t := by
  constructor
  · intro he z hz _
    simpa [he] using hz
  · intro h
    apply Set.Subset.antisymm _ (ExtendedImageHull.sound _)
    intro z hz
    by_cases hl : ExtendedImageHull.lower (values P Q t) < (z : EReal)
    · by_cases hu : (z : EReal) < ExtendedImageHull.upper (values P Q t)
      · exact interior_attained hp hq t hl hu
      · exact h z hz (Or.inr (le_antisymm hz.2 (le_of_not_gt hu)))
    · exact h z hz (Or.inl (le_antisymm (le_of_not_gt hl) hz.1))

/-- A conversion of the enclosing tagged family preserves literal exceptional
tags exactly; extended hull endpoints do not add such values. -/
theorem tagged_hull {n} (P : Set ℝ) (Q : Fin n → Set ℝ) (t : Fin n → ℝ)
    (S : Set ExceptionalComparisons.Value)
    (h : TaggedConversion.finitePart S = values P Q t) :
    TaggedConversion.finitePart (TaggedConversion.lift ExtendedImageHull.hull S) =
      ExtendedImageHull.hull (values P Q t) ∧
    ((.negInf ∈ TaggedConversion.lift ExtendedImageHull.hull S ↔ .negInf ∈ S) ∧
     (.posInf ∈ TaggedConversion.lift ExtendedImageHull.hull S ↔ .posInf ∈ S) ∧
     (.undefined ∈ TaggedConversion.lift ExtendedImageHull.hull S ↔ .undefined ∈ S)) := by
  exact ⟨by rw [TaggedConversion.finitePart_lift,h],
    TaggedConversion.exceptional_exact _ _⟩

/-- Reuse the same-parameter demotion theorem with the actual coefficient witness
and its exact domain; do not manufacture a value for an empty coefficient. -/
theorem hull_sound {n} (P : Set ℝ) (Q : Fin n → Set ℝ) :
    GeneralFamilyDemotion.Sound (fun t => ExtendedImageHull.hull (values P Q t))
      (exactInputDomain (fun _ w => admissible P Q w) (fun t w z => z=value w t))
      (fun _ w => admissible P Q w) (fun t w z => z=value w t) :=
  GeneralFamilyDemotion.exact_hull_sound _ _

end GeneralizedIntervalArithmetic.HansenRealSets
