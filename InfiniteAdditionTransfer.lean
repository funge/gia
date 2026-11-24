import TaggedConversion

/-! Exact transfer of the already modeled right-positive-infinity addition rows.
No completion of the source exceptional table or IEEE interpretation. -/
namespace GeneralizedIntervalArithmetic.InfiniteAdditionTransfer
open ExceptionalComparisons
local notation "Tag" => ExceptionalComparisons.Value

def observations (S : Set Tag) : Set (Option Tag) :=
  (fun x => addObservation x .posInf) '' S

def results (S : Set Tag) : Set Tag := {v | some v ∈ observations S}

/-- Exact graph retains unmodeled observations as `none`, not as lambda. -/
theorem graph (S : Set Tag) (r : Option Tag) : r ∈ observations S ↔
    (r = some .posInf ∧ ((TaggedConversion.finitePart S).Nonempty ∨ .posInf ∈ S)) ∨
    (r = none ∧ (.negInf ∈ S ∨ .undefined ∈ S)) := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    cases x with
    | finite x => exact Or.inl ⟨rfl,Or.inl ⟨x,hx⟩⟩
    | posInf => exact Or.inl ⟨rfl,Or.inr hx⟩
    | negInf => exact Or.inr ⟨rfl,Or.inl hx⟩
    | undefined => exact Or.inr ⟨rfl,Or.inr hx⟩
  · rintro (⟨rfl,⟨x,hx⟩ | hx⟩ | ⟨rfl,hx | hx⟩)
    · exact ⟨.finite x,hx,rfl⟩
    · exact ⟨.posInf,hx,rfl⟩
    · exact ⟨.negInf,hx,rfl⟩
    · exact ⟨.undefined,hx,rfl⟩

theorem result_iff (S : Set Tag) (v : Tag) : v ∈ results S ↔
    v = .posInf ∧ ((TaggedConversion.finitePart S).Nonempty ∨ .posInf ∈ S) := by
  change some v ∈ observations S ↔ _
  rw [graph]
  simp

theorem missing_iff (S : Set Tag) : none ∈ observations S ↔
    .negInf ∈ S ∨ .undefined ∈ S := by rw [graph]; simp

/-- Sufficient exact conversion criterion: preserve finite-value existence and
retain exceptional tags. This does not assert equality of operand witnesses. -/
theorem conversion_exact (C : Set ℝ → Set ℝ)
    (hc : ∀ S, (C S).Nonempty ↔ S.Nonempty) (S : Set Tag) :
    observations (TaggedConversion.lift C S) = observations S := by
  ext r
  rw [graph,graph,TaggedConversion.finitePart_lift,hc]
  rfl

/-- Concrete finite-hull conversion discharges the existence premise, including
empty and unbounded finite payloads. -/
theorem hull_observations (S : Set Tag) :
    observations (TaggedConversion.lift ExtendedImageHull.hull S) = observations S :=
  conversion_exact _ ExtendedImageHull.nonempty_iff S

theorem finite_results_empty (S : Set Tag) : TaggedConversion.finitePart (results S) = ∅ := by
  ext x
  change .finite x ∈ results S ↔ False
  rw [result_iff]
  simp

/-- Hull conversion of the successful outputs is exact: they contain no finite
payload and at most the literal positive-infinity tag. -/
theorem result_hull_fixed (S : Set Tag) :
    TaggedConversion.lift ExtendedImageHull.hull (results S) = results S := by
  ext v
  cases v with
  | finite x =>
    change x ∈ ExtendedImageHull.hull (TaggedConversion.finitePart (results S)) ↔
      .finite x ∈ results S
    rw [finite_results_empty,ExtendedImageHull.empty_hull,result_iff]
    simp
  | negInf => rfl
  | posInf => rfl
  | undefined => rfl

/-- Exact commutation for this operator, not a homomorphism for arbitrary
exceptional arithmetic or all family conversions. -/
theorem hull_commutes (S : Set Tag) :
    results (TaggedConversion.lift ExtendedImageHull.hull S) =
      TaggedConversion.lift ExtendedImageHull.hull (results S) := by
  rw [result_hull_fixed]
  ext v
  change some v ∈ observations (TaggedConversion.lift ExtendedImageHull.hull S) ↔
    some v ∈ observations S
  rw [hull_observations]

/-- A family is converted at the same parameter. Missing coverage is preserved
in addition to the successful result set. -/
theorem family_transfer {α : Type*} (S : α → Set Tag) (p : α) :
    results (TaggedConversion.lift ExtendedImageHull.hull (S p)) =
      TaggedConversion.lift ExtendedImageHull.hull (results (S p)) ∧
    (none ∈ observations (TaggedConversion.lift ExtendedImageHull.hull (S p)) ↔
      none ∈ observations (S p)) :=
  ⟨hull_commutes _,by rw [hull_observations]⟩

end GeneralizedIntervalArithmetic.InfiniteAdditionTransfer
