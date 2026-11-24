import ExceptionalComparisons

/-! Source-backed expression cases, separate from extended bounds on real sets.
No unspecified exceptional operator table is completed here. -/
namespace GeneralizedIntervalArithmetic.ExceptionalFamilies
open ExceptionalComparisons

/-- Observe the syntactic expression a − b·t. The exceptional row is ONLY
Tupper §2.9.5's explicit midpoint example, not inferred primitive arithmetic. -/
noncomputable def differenceScaled : ExceptionalComparisons.Value → ExceptionalComparisons.Value → ℝ → Option ExceptionalComparisons.Value := by
  classical
  exact fun a b t => match a,b with
    | .finite x,.finite y => some (.finite (x-y*t))
    | .posInf,.posInf => if t=1/2 then some .undefined else none
    | _,_ => none

theorem finite_agreement (a b t : ℝ) :
    differenceScaled (.finite a) (.finite b) t = some (.finite (a-b*t)) := rfl

theorem source_midpoint : differenceScaled .posInf .posInf (1/2) = some .undefined := by
  simp [differenceScaled]

theorem other_parameters_unmodeled {t : ℝ} (ht : t≠1/2) :
    differenceScaled .posInf .posInf t = none := by simp only [differenceScaled,if_neg ht]

theorem lambda_input_unmodeled (b : ExceptionalComparisons.Value) (t : ℝ) :
    differenceScaled .undefined b t = none := by cases b <;> rfl

/-- Only finite payloads supply actual real output witnesses. This is NOT
an enclosure interpretation of infinity or a domain classifier on `none`,
and is not the source numerical '='. -/
noncomputable def realOutputs : Option ExceptionalComparisons.Value → Set ℝ
  | some (.finite x) => {x}
  | _ => ∅

theorem literal_midpoint_no_real :
    realOutputs (differenceScaled .posInf .posInf (1/2)) = ∅ := by
  rw [source_midpoint]; rfl

/-- An infinite upper bound is not itself an admitted real value. -/
theorem bound_semantics :
    ExtendedImageHull.interval ⊥ ⊤ = Set.univ ∧
    ExtendedImageHull.interval (0:EReal) ⊤ = Set.Ici (0:ℝ) ∧
    ExtendedImageHull.interval ⊤ ⊤ = ∅ := by
  constructor
  · ext x; simp [ExtendedImageHull.interval]
  constructor
  · ext x; simp [ExtendedImageHull.interval]
  · ext x; simp [ExtendedImageHull.interval]

/-- Source §2.7.4's universal bound encloses any total real-valued result. -/
theorem universal_encloses {α : Type*} (f : α → ℝ) (x : α) :
    f x ∈ ExtendedImageHull.interval ⊥ ⊤ := by simp [ExtendedImageHull.interval]

/-- Two separately varying, nonnegative real coefficient witnesses. -/
noncomputable def independentImage : Set ℝ :=
  {z | ∃a b:ℝ, 0≤a ∧ 0≤b ∧ z=a-b*(1/2)}

/-- Same coefficient witness in both occurrences: no Cartesian replacement. -/
noncomputable def sharedImage : Set ℝ :=
  {z | ∃a:ℝ, 0≤a ∧ z=a-a*(1/2)}

theorem independent_exact : independentImage = Set.univ := by
  ext z
  simp only [Set.mem_univ,iff_true]
  by_cases hz : 0≤z
  · exact ⟨z,0,hz,le_rfl,by ring⟩
  · exact ⟨0,-2*z,le_rfl,by linarith,by ring⟩

theorem shared_exact : sharedImage = Set.Ici (0:ℝ) := by
  ext z
  constructor
  · rintro ⟨a,ha,rfl⟩
    change 0≤a-a*(1/2)
    linarith
  · intro hz
    exact ⟨2*z,by change 0≤z at hz; linarith,by ring⟩

/-- Bounds are exact for these real-output images. No tag evaluation occurs. -/
theorem images_as_bounds :
    independentImage = ExtendedImageHull.interval ⊥ ⊤ ∧
    sharedImage = ExtendedImageHull.interval 0 ⊤ := by
  rw [independent_exact,shared_exact,bound_semantics.1,bound_semantics.2.1]
  exact ⟨rfl,rfl⟩

/-- Replacing unbounded coefficient families by literal +∞ operands does NOT
commute with the source's specified expression evaluation. -/
theorem replacement_not_commuting :
    independentImage ≠ realOutputs (differenceScaled .posInf .posInf (1/2)) ∧
    sharedImage ≠ realOutputs (differenceScaled .posInf .posInf (1/2)) := by
  rw [literal_midpoint_no_real,independent_exact,shared_exact]
  constructor
  · exact Set.univ_nonempty.ne_empty
  · exact (show (Set.Ici (0:ℝ)).Nonempty from ⟨0,by simp⟩).ne_empty

/-- The source's undefined tag does not supply even an extended numeric bound. -/
theorem midpoint_has_no_bound :
    (differenceScaled .posInf .posInf (1/2)).bind bound = none := by
  rw [source_midpoint]; rfl

/-- mathlib's EReal arithmetic is suitable for ordered bounds, but its chosen
exceptional subtraction convention is NOT Tupper's literal expression semantics. -/
theorem ereal_evaluation_disagrees :
    (⊤ : EReal) - ⊤ * ((1/2:ℝ):EReal) = ⊥ ∧
    (differenceScaled .posInf .posInf (1/2)).bind bound = none := by
  refine ⟨?_,midpoint_has_no_bound⟩
  rw [EReal.top_mul_coe_of_pos (by norm_num : (0:ℝ)<1/2),EReal.sub_top]

/-- Missing observation and modeled undefinedness are distinct before projection
onto real witnesses, even though neither supplies a real value. -/
theorem missing_not_undefined :
    differenceScaled .posInf .posInf 0 ≠ differenceScaled .posInf .posInf (1/2) ∧
    realOutputs (differenceScaled .posInf .posInf 0) =
      realOutputs (differenceScaled .posInf .posInf (1/2)) := by
  simp [differenceScaled,realOutputs]

end GeneralizedIntervalArithmetic.ExceptionalFamilies
