import CoefficientWitnesses

/-! Finite closed real-choice specialization of Tupper §2.14's displayed
Hansen form. Pointwise coefficient choice and joint use witnesses are separate. -/
namespace GeneralizedIntervalArithmetic.HansenCoefficients
open scoped BigOperators

abbrev Choice (n : ℕ) := ℝ × (Fin n → ℝ)
def admissible {n} (P : QInterval) (Q : Fin n → QInterval) (w : Choice n) : Prop :=
  P.Contains w.1 ∧ ∀ i, (Q i).Contains (w.2 i)
noncomputable def value {n} (w : Choice n) (t : Fin n → ℝ) : ℝ :=
  w.1 + ∑ i, w.2 i*t i

def values {n} (P : QInterval) (Q : Fin n → QInterval) (t : Fin n → ℝ) : Set ℝ :=
  IntervalSetDenotation.denote (fun w : Choice n => fun s => {value w s})
    {w | admissible P Q w} t

theorem mem_values {n} (P : QInterval) (Q : Fin n → QInterval) (t : Fin n → ℝ) (z : ℝ) :
    z ∈ values P Q t ↔ ∃ w, admissible P Q w ∧ z=value w t := by
  rfl

noncomputable def lowChoice {n} (P : QInterval) (Q : Fin n → QInterval) (t : Fin n → ℝ) : Choice n :=
  ⟨P.lo, fun i => if 0 ≤ t i then (Q i).lo else (Q i).hi⟩
noncomputable def highChoice {n} (P : QInterval) (Q : Fin n → QInterval) (t : Fin n → ℝ) : Choice n :=
  ⟨P.hi, fun i => if 0 ≤ t i then (Q i).hi else (Q i).lo⟩
noncomputable def lower {n} (P : QInterval) (Q : Fin n → QInterval) (t : Fin n → ℝ) : ℝ :=
  value (lowChoice P Q t) t
noncomputable def upper {n} (P : QInterval) (Q : Fin n → QInterval) (t : Fin n → ℝ) : ℝ :=
  value (highChoice P Q t) t

theorem choices_admissible {n} (P : QInterval) (Q : Fin n → QInterval) (t : Fin n → ℝ) :
    admissible P Q (lowChoice P Q t) ∧ admissible P Q (highChoice P Q t) := by
  have hp : (P.lo:ℝ) ≤ P.hi := by exact_mod_cast P.ordered
  have hq (i) : ((Q i).lo:ℝ) ≤ (Q i).hi := by exact_mod_cast (Q i).ordered
  constructor
  · refine ⟨⟨le_rfl,hp⟩,?_⟩
    intro i
    dsimp [lowChoice]
    split_ifs <;> exact ⟨by first | exact le_rfl | exact hq i,by first | exact le_rfl | exact hq i⟩
  · refine ⟨⟨hp,le_rfl⟩,?_⟩
    intro i
    dsimp [highChoice]
    split_ifs <;> exact ⟨by first | exact le_rfl | exact hq i,by first | exact le_rfl | exact hq i⟩

theorem encloses {n} {P : QInterval} {Q : Fin n → QInterval} {w : Choice n}
    (hw : admissible P Q w) (t : Fin n → ℝ) :
    lower P Q t ≤ value w t ∧ value w t ≤ upper P Q t := by
  constructor
  · apply add_le_add hw.1.1
    apply Finset.sum_le_sum
    intro i _
    dsimp [lowChoice]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right (hw.2 i).1 h
    · exact mul_le_mul_of_nonpos_right (hw.2 i).2 (le_of_not_ge h)
  · apply add_le_add hw.1.2
    apply Finset.sum_le_sum
    intro i _
    dsimp [highChoice]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right (hw.2 i).2 h
    · exact mul_le_mul_of_nonpos_right (hw.2 i).1 (le_of_not_ge h)

theorem attained {n} (P : QInterval) (Q : Fin n → QInterval) (t : Fin n → ℝ) :
    lower P Q t ∈ values P Q t ∧ upper P Q t ∈ values P Q t :=
  ⟨⟨lowChoice P Q t,(choices_admissible P Q t).1,rfl⟩,
   ⟨highChoice P Q t,(choices_admissible P Q t).2,rfl⟩⟩

theorem mix_contains {I : QInterval} {x y s : ℝ} (hx : I.Contains x) (hy : I.Contains y)
    (hs : s ∈ Set.Icc (0:ℝ) 1) : I.Contains ((1-s)*x+s*y) := by
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hx.1 (sub_nonneg.mpr hs.2),
      mul_le_mul_of_nonneg_left hy.1 hs.1]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2 (sub_nonneg.mpr hs.2),
      mul_le_mul_of_nonneg_left hy.2 hs.1]

noncomputable def mix {n} (a b : Choice n) (s : ℝ) : Choice n :=
  ⟨(1-s)*a.1+s*b.1, fun i => (1-s)*a.2 i+s*b.2 i⟩

theorem mix_admissible {n} {P : QInterval} {Q : Fin n → QInterval} {a b : Choice n}
    (ha : admissible P Q a) (hb : admissible P Q b) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    admissible P Q (mix a b s) :=
  ⟨mix_contains ha.1 hb.1 hs, fun i => mix_contains (ha.2 i) (hb.2 i) hs⟩

/-- Every interior value is attained by interpolating the two coefficient
witnesses, not by assuming that a sound enclosure is an exact image. -/
theorem exact_interval {n} (P : QInterval) (Q : Fin n → QInterval) (t : Fin n → ℝ) :
    values P Q t = Set.Icc (lower P Q t) (upper P Q t) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact encloses hw t
  · intro hz
    let f : ℝ → ℝ := fun s => value (mix (lowChoice P Q t) (highChoice P Q t) s) t
    have hf : ContinuousOn f (Set.Icc 0 1) := by
      dsimp [f,value,mix]
      fun_prop
    have h0 : f 0 = lower P Q t := by simp [f,mix,value,lower]
    have h1 : f 1 = upper P Q t := by simp [f,mix,value,upper]
    obtain ⟨s,hs,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hf
      (show z ∈ Set.Icc (f 0) (f 1) by simpa [h0,h1] using hz)
    exact ⟨mix (lowChoice P Q t) (highChoice P Q t) s,
      mix_admissible (choices_admissible P Q t).1 (choices_admissible P Q t).2 hs,he.symm⟩

/-- Literal two-point parameter restriction printed in §2.14. No nonnegative
radius assumption is needed for this set or the pointwise theorem. -/
def SignedDomain {n} (c t : Fin n → ℝ) : Prop := ∀ i, t i = -c i ∨ t i = c i

theorem signed_exact {n} (P : QInterval) (Q : Fin n → QInterval) (c t : Fin n → ℝ)
    (_ht : SignedDomain c t) : values P Q t = Set.Icc (lower P Q t) (upper P Q t) :=
  exact_interval P Q t

/-- Keep a single whole coefficient witness outside the collection of uses. -/
def realizes {n} (P : QInterval) (Q : Fin n → QInterval) (T : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) : Prop := ∃ w, admissible P Q w ∧ ∀ t ∈ T, f t=value w t

theorem realized_pointwise {n} {P : QInterval} {Q : Fin n → QInterval}
    {T : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} (h : realizes P Q T f) :
    ∀ t ∈ T, f t ∈ Set.Icc (lower P Q t) (upper P Q t) := by
  obtain ⟨w,hw,hf⟩ := h
  intro t ht
  rw [hf t ht]
  exact encloses hw t

/-- One-dimensional compatibility with the existing persistent coefficient model. -/
theorem one_parameter (P Q : QInterval) (T : Set ℝ) (f : ℝ → ℝ) :
    realizes P (fun _ : Fin 1 => Q) {t | t 0 ∈ T} (fun t => f (t 0)) ↔
    CoefficientWitnesses.realizes (CoefficientWitnesses.intervalPairs P Q) T f := by
  constructor
  · rintro ⟨⟨p,q⟩,⟨hp,hq⟩,hf⟩
    refine ⟨(p,q 0),⟨hp,hq 0⟩,?_⟩
    intro t ht
    simpa [value] using hf (fun _=>t) ht
  · rintro ⟨⟨p,q⟩,⟨hp,hq⟩,hf⟩
    refine ⟨(p,fun _=>q),⟨hp,fun _=>hq⟩,?_⟩
    intro t ht
    simpa [value] using hf (t 0) ht

end GeneralizedIntervalArithmetic.HansenCoefficients
