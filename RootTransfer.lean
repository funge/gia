import TaggedConversion

/-! Partial square root through finite-real hull conversion. Literal exceptional
inputs retain the existing unmodeled observations; no new arithmetic rows. -/
namespace GeneralizedIntervalArithmetic.RootTransfer
open ExceptionalComparisons
local notation "Tag" => ExceptionalComparisons.Value

def roots (S : Set ℝ) : Set ℝ :=
  {z | SqrtValues (fun (_ : Unit) (_ : Unit) x => x ∈ S) () () z}

theorem root_iff (S : Set ℝ) (z : ℝ) : z ∈ roots S ↔ 0 ≤ z ∧ z^2 ∈ S := by
  constructor
  · rintro ⟨x,hx,h0,rfl⟩
    exact ⟨Real.sqrt_nonneg _,by rw [Real.sq_sqrt h0]; exact hx⟩
  · rintro ⟨hz,h⟩
    exact ⟨z^2,h,sq_nonneg _,by rw [Real.sqrt_sq hz]⟩

theorem roots_mono {S T : Set ℝ} (h : S ⊆ T) : roots S ⊆ roots T := by
  rintro z ⟨x,hx,h0,hz⟩
  exact ⟨x,h hx,h0,hz⟩

/-- Same actual input witness gives a sound output after hull conversion.
This does not claim that newly admitted inputs occur in the original family. -/
theorem hull_sound (S : Set ℝ) : roots S ⊆ ExtendedImageHull.hull
    (roots (ExtendedImageHull.hull S)) :=
  (roots_mono (ExtendedImageHull.sound S)).trans (ExtendedImageHull.sound _)

/-- Exactness is equivalent to the absence of newly admitted nonnegative input
values, not merely preservation of input nonemptiness. -/
theorem exact_iff (S : Set ℝ) : roots (ExtendedImageHull.hull S) = roots S ↔
    ∀ x ∈ ExtendedImageHull.hull S, 0 ≤ x → x ∈ S := by
  constructor
  · intro h x hx h0
    have hr : Real.sqrt x ∈ roots (ExtendedImageHull.hull S) := ⟨x,hx,h0,rfl⟩
    rw [h,root_iff] at hr
    simpa [Real.sq_sqrt h0] using hr.2
  · intro h
    apply Set.Subset.antisymm _ (roots_mono (ExtendedImageHull.sound S))
    intro z hz
    rw [root_iff] at hz ⊢
    exact ⟨hz.1,h _ hz.2 (sq_nonneg _)⟩

theorem interval_exact (l u : EReal) :
    roots (ExtendedImageHull.hull (ExtendedImageHull.interval l u)) =
      roots (ExtendedImageHull.interval l u) := by rw [ExtendedImageHull.interval_fixed]

/-- Hull conversion cannot introduce negative inputs unless some negative
input already existed. Unlike the nonnegative domain, this is a strict test. -/
theorem negative_iff (S : Set ℝ) :
    (∃ x ∈ ExtendedImageHull.hull S, x < 0) ↔ ∃ x ∈ S, x < 0 := by
  constructor
  · rintro ⟨x,hx,hx0⟩
    by_contra h
    push_neg at h
    have hs : S ⊆ ExtendedImageHull.interval 0 ⊤ := by
      intro y hy
      exact ⟨by exact_mod_cast h y hy,le_top⟩
    have hh := ExtendedImageHull.least hs hx
    have : (0:ℝ) ≤ x := by exact_mod_cast hh.1
    linarith
  · rintro ⟨x,hx,h0⟩
    exact ⟨x,ExtendedImageHull.sound S hx,h0⟩

def observations (S : Set Tag) : Set (Option Tag) := sqrtObservation '' S

theorem finite_graph (S : Set Tag) (z : ℝ) :
    some (.finite z) ∈ observations S ↔ z ∈ roots (TaggedConversion.finitePart S) := by
  constructor
  · rintro ⟨v,hv,he⟩
    cases v with
    | finite x =>
      have h := (sqrt_finite_agreement x z).mp he
      obtain ⟨y,hy,h0,hz⟩ := h
      subst y
      exact ⟨x,hv,h0,hz⟩
    | negInf => simp [sqrtObservation] at he
    | posInf => simp [sqrtObservation] at he
    | undefined => simp [sqrtObservation] at he
  · rintro ⟨x,hx,h0,hz⟩
    exact ⟨.finite x,hx,(sqrt_finite_agreement x z).mpr ⟨x,rfl,h0,hz⟩⟩

theorem lambda_graph (S : Set Tag) : some .undefined ∈ observations S ↔
    ∃ x ∈ TaggedConversion.finitePart S, x < 0 := by
  constructor
  · rintro ⟨v,hv,he⟩
    cases v with
    | finite x =>
      by_cases h : x < 0
      · exact ⟨x,hv,h⟩
      · simp [sqrtObservation,h] at he
    | negInf => simp [sqrtObservation] at he
    | posInf => simp [sqrtObservation] at he
    | undefined => simp [sqrtObservation] at he
  · rintro ⟨x,hx,h⟩
    exact ⟨.finite x,hx,sqrt_negative x h⟩

theorem missing_graph (S : Set Tag) : none ∈ observations S ↔
    .negInf ∈ S ∨ .posInf ∈ S ∨ .undefined ∈ S := by
  constructor
  · rintro ⟨v,hv,he⟩
    cases v with
    | finite x => simp only [sqrtObservation] at he; split_ifs at he
    | negInf => exact Or.inl hv
    | posInf => exact Or.inr (Or.inl hv)
    | undefined => exact Or.inr (Or.inr hv)
  · rintro (h | h | h)
    · exact ⟨.negInf,h,rfl⟩
    · exact ⟨.posInf,h,rfl⟩
    · exact ⟨.undefined,h,rfl⟩

theorem no_infinite_results (S : Set Tag) :
    some .negInf ∉ observations S ∧ some .posInf ∉ observations S := by
  constructor <;> rintro ⟨v,_,he⟩ <;> cases v <;>
    simp only [sqrtObservation] at he
  all_goals first | contradiction | (split_ifs at he <;> simp_all)

/-- All original observations survive, including lambda and missing coverage. -/
theorem observations_sound (S : Set Tag) :
    observations S ⊆ observations (TaggedConversion.lift ExtendedImageHull.hull S) := by
  rintro r ⟨v,hv,hr⟩
  exact ⟨v,TaggedConversion.lift_sound _ ExtendedImageHull.sound _ hv,hr⟩

theorem statuses_exact (S : Set Tag) :
    (some .undefined ∈ observations (TaggedConversion.lift ExtendedImageHull.hull S) ↔
      some .undefined ∈ observations S) ∧
    (none ∈ observations (TaggedConversion.lift ExtendedImageHull.hull S) ↔
      none ∈ observations S) := by
  constructor
  · rw [lambda_graph,lambda_graph,TaggedConversion.finitePart_lift,negative_iff]
  · rw [missing_graph,missing_graph]; rfl

/-- Exact observation equality iff no new nonnegative finite input is admitted.
Literal infinities and lambda inputs remain unmodeled, not assigned roots. -/
theorem observations_exact_iff (S : Set Tag) :
    observations (TaggedConversion.lift ExtendedImageHull.hull S) = observations S ↔
    ∀ x ∈ ExtendedImageHull.hull (TaggedConversion.finitePart S),
      0 ≤ x → x ∈ TaggedConversion.finitePart S := by
  constructor
  · intro h
    apply (exact_iff _).mp
    ext z
    rw [← finite_graph S z,← h,finite_graph,TaggedConversion.finitePart_lift]
  · intro h
    have hr := (exact_iff _).mpr h
    ext r
    cases r with
    | none => exact (statuses_exact S).2
    | some v =>
      cases v with
      | finite z => rw [finite_graph,finite_graph,TaggedConversion.finitePart_lift,hr]
      | negInf => simp [(no_infinite_results _).1]
      | posInf => simp [(no_infinite_results _).2]
      | undefined => exact (statuses_exact S).1

/-- An actual partial-expression root keeps its original parameter and input
witness when transferred into the converted enclosure. -/
theorem witness_transfer {α W : Type*} (S : α → Set ℝ)
    (R : α → W → ℝ → Prop) (p : α) (w : W)
    (hi : ∀ x, R p w x → x ∈ S p) {z : ℝ} (hz : SqrtValues R p w z) :
    z ∈ ExtendedImageHull.hull (roots (ExtendedImageHull.hull (S p))) := by
  obtain ⟨x,hx,h0,he⟩ := hz
  exact hull_sound (S p) ⟨x,hi x hx,h0,he⟩

end GeneralizedIntervalArithmetic.RootTransfer
