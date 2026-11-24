import IntervalCoefficientVariants

/-! A fixed-coefficient-witness interpretation, explicitly separate from the
pointwise coefficient intervals in §2.14. No persistent-choice convention is
attributed to the source merely from equality of interval descriptions. -/
namespace GeneralizedIntervalArithmetic.CoefficientWitnesses

/-- One admissible pair for all uses on T, with no assertion outside T. -/
def realizes (C : Set (ℝ × ℝ)) (T : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ c ∈ C, ∀ t ∈ T, f t = c.1+c.2*t

/-- Heterogeneous coefficient codes keep their pair constraint and one witness. -/
def coded {A B : Type*} (p : A → ℝ) (q : B → ℝ) (C : Set (A × B))
    (T : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ c ∈ C, ∀ t ∈ T, f t = p c.1+q c.2*t

def decodePairs {A B : Type*} (p : A → ℝ) (q : B → ℝ) (C : Set (A × B)) : Set (ℝ × ℝ) :=
  (fun c => (p c.1,q c.2)) '' C

/-- Exact conversion, without replacing a constrained pair by independent marginals. -/
theorem coded_exact {A B : Type*} (p : A → ℝ) (q : B → ℝ) (C : Set (A × B))
    (T : Set ℝ) (f : ℝ → ℝ) :
    coded p q C T f ↔ realizes (decodePairs p q C) T f := by
  constructor
  · rintro ⟨c,hc,hf⟩
    exact ⟨(p c.1,q c.2),⟨c,hc,rfl⟩,hf⟩
  · rintro ⟨_,⟨c,hc,rfl⟩,hf⟩
    exact ⟨c,hc,hf⟩

/-- Two distinct anchor uses recover the coefficients. The convenient 0/1
anchors match QAffine's endpoint basis. No choice is repeated at an interior t. -/
theorem realizes_iff (C : Set (ℝ × ℝ)) (T : Set ℝ) (f : ℝ → ℝ)
    (h0 : 0 ∈ T) (h1 : 1 ∈ T) :
    realizes C T f ↔ (f 0,f 1-f 0) ∈ C ∧
      ∀ t ∈ T, f t = (1-t)*f 0+t*f 1 := by
  constructor
  · rintro ⟨⟨p,q⟩,hc,hf⟩
    have e0 : f 0 = p := by simpa using hf 0 h0
    have e1 : f 1 = p+q := by simpa using hf 1 h1
    refine ⟨by simpa [e0,e1] using hc,?_⟩
    intro t ht
    rw [hf t ht,e0,e1]
    ring
  · rintro ⟨hc,hf⟩
    refine ⟨(f 0,f 1-f 0),hc,?_⟩
    intro t ht
    rw [hf t ht]
    ring

theorem coded_iff {A B : Type*} (p : A → ℝ) (q : B → ℝ) (C : Set (A × B))
    (T : Set ℝ) (f : ℝ → ℝ) (h0 : 0 ∈ T) (h1 : 1 ∈ T) :
    coded p q C T f ↔
      (∃ c ∈ C, p c.1 = f 0 ∧ q c.2 = f 1-f 0) ∧
      ∀ t ∈ T, f t = (1-t)*f 0+t*f 1 := by
  rw [coded_exact,realizes_iff _ _ _ h0 h1]
  simp [decodePairs,Prod.mk.injEq]

/-- Different carriers: integral intercept and rational slope. This is an
exact model-level correspondence, not an IEEE conversion or an endpoint claim. -/
theorem integer_rational_iff (T : Set ℝ) (f : ℝ → ℝ) (h0 : 0 ∈ T) (h1 : 1 ∈ T) :
    coded (fun p : ℤ => (p:ℝ)) (fun q : ℚ => (q:ℝ)) Set.univ T f ↔
      (∃ p : ℤ, (p:ℝ)=f 0) ∧ (∃ q : ℚ, (q:ℝ)=f 1-f 0) ∧
      ∀ t ∈ T, f t = (1-t)*f 0+t*f 1 := by
  rw [coded_iff _ _ _ _ _ h0 h1]
  constructor
  · rintro ⟨⟨⟨p,q⟩,_,hp,hq⟩,hf⟩
    exact ⟨⟨p,hp⟩,⟨q,hq⟩,hf⟩
  · rintro ⟨⟨p,hp⟩,⟨q,hq⟩,hf⟩
    exact ⟨⟨(p,q),Set.mem_univ _,hp,hq⟩,hf⟩

/-- Restriction preserves a witness; empty coefficient domains never invent one. -/
theorem restrict {C : Set (ℝ × ℝ)} {S T : Set ℝ} {f : ℝ → ℝ}
    (h : realizes C T f) (hst : S ⊆ T) : realizes C S f := by
  obtain ⟨c,hc,hf⟩ := h
  exact ⟨c,hc,fun t ht => hf t (hst ht)⟩

theorem empty_parameters (C : Set (ℝ × ℝ)) (f : ℝ → ℝ) :
    realizes C ∅ f ↔ C.Nonempty := by
  constructor
  · rintro ⟨c,hc,_⟩; exact ⟨c,hc⟩
  · rintro ⟨c,hc⟩; exact ⟨c,hc,fun _ h => False.elim h⟩

theorem no_coefficients (T : Set ℝ) (f : ℝ → ℝ) : ¬ realizes ∅ T f := by
  simp [realizes]

/-- Joint finite/infinite samples retain the pair existential outside all uses. -/
def samples {ι : Type*} (C : Set (ℝ × ℝ)) (ts : ι → ℝ) : Set (ι → ℝ) :=
  {v | ∃ c ∈ C, ∀ i, v i = c.1+c.2*ts i}

theorem sample_realization {ι : Type*} {C : Set (ℝ × ℝ)} {T : Set ℝ} {f : ℝ → ℝ}
    (h : realizes C T f) (ts : ι → ℝ) (ht : ∀ i, ts i ∈ T) :
    (fun i => f (ts i)) ∈ samples C ts := by
  obtain ⟨c,hc,hf⟩ := h
  exact ⟨c,hc,fun i => hf (ts i) (ht i)⟩

/-- Existing piece semantics is the marginal of the shared-witness interpretation. -/
def marginal (C : Set (ℝ × ℝ)) (t : ℝ) : Set ℝ :=
  IntervalSetDenotation.denote (fun c : ℝ × ℝ => fun s => {c.1+c.2*s}) C t

theorem samples_enclosed {ι : Type*} {C : Set (ℝ × ℝ)} {ts : ι → ℝ} {v : ι → ℝ}
    (h : v ∈ samples C ts) : ∀ i, v i ∈ marginal C (ts i) := by
  obtain ⟨c,hc,hv⟩ := h
  intro i
  exact ⟨c,hc,hv i⟩

def intervalPairs (P Q : QInterval) : Set (ℝ × ℝ) :=
  {p | P.Contains p} ×ˢ {q | Q.Contains q}

theorem interval_marginal (P Q : QInterval) (t : ℝ) :
    marginal (intervalPairs P Q) t = IntervalCoefficientVariants.values P Q t := rfl

/-- Reuse the existing exact pointwise enclosure, without claiming that its
independent marginals reconstruct one coherent trajectory. -/
theorem realized_form {P Q : QInterval} {T : Set ℝ} {f : ℝ → ℝ}
    (h : realizes (intervalPairs P Q) T f) {t : ℝ} (ht : t ∈ T) (hn : 0 ≤ t) :
    (IntervalCoefficientVariants.form P Q).Contains t (f t) := by
  obtain ⟨⟨p,q⟩,⟨hp,hq⟩,hf⟩ := h
  apply (IntervalCoefficientVariants.exact_form P Q hn (f t)).mp
  exact (IntervalCoefficientVariants.mem_values P Q t (f t)).mpr ⟨p,q,hp,hq,hf t ht⟩

end GeneralizedIntervalArithmetic.CoefficientWitnesses
