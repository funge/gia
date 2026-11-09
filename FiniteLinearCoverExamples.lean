import FiniteLinearCovers
import PiecewiseExamples

namespace GeneralizedIntervalArithmetic.FiniteLinearCoverExamples
open PiecewiseExamples

def separated : FiniteLinearCover := [constantModel (-2), constantModel 3]
def branchValues := PiecewiseValues (fun t => t < (1/2:ℝ))
  (fun t z => Value t t (.const (-2)) z) (fun t z => Value t t (.const 3) z)

private theorem parameter_contains (t : ℝ) : parameter.Contains t t := by
  apply (linear_exact_contains _ _ _).mpr
  simp [QAffine.value]

theorem evaluated_branches_cover : separated.Covers branchValues := by
  exact cover_select (c := .unknown) trivial
    (cover_guarded (X := parameter) (Y := parameter)
      (fun t _ => parameter_contains t) (fun t _ => parameter_contains t) rfl)
    (cover_guarded (X := parameter) (Y := parameter)
      (fun t _ => parameter_contains t) (fun t _ => parameter_contains t) rfl)

theorem separated_away : ∀ I ∈ separated, I.hull.AwayZero := by
  intro I hi
  rcases List.mem_cons.mp hi with rfl | hi
  · decide +kernel
  · rcases List.mem_singleton.mp hi with rfl
    decide +kernel

theorem evaluated_branches_exclude_zero {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ¬ branchValues t 0 := cover_excludes_zero evaluated_branches_cover separated_away ht

theorem joined_reciprocal_unknown :
    ((constantModel (-2)).join (constantModel 3)).recip? = none := by
  apply Option.not_isSome_iff_eq_none.mp
  decide +kernel

theorem separated_reciprocal_succeeds : separated.recip?.isSome := by decide +kernel

theorem reciprocal_branches_enclosed :
    ∃ D, separated.recip? = some D ∧
      D.Covers (QuotientValues (fun _ z => z = 1) branchValues) := by
  cases h : separated.recip? with
  | none =>
    have hs := separated_reciprocal_succeeds
    simp [h] at hs
  | some D => exact ⟨D, rfl, cover_recip_sound evaluated_branches_cover h⟩

theorem zero_component_unknown :
    FiniteLinearCover.recip? [constantModel (-2), constantModel 0] = none := by
  apply Option.not_isSome_iff_eq_none.mp
  decide +kernel

/-- Overapproximation is compatible with an empty actual domain. -/
theorem nonempty_cover_of_no_values : separated ≠ [] ∧ separated.Covers (fun _ _ => False) := by
  exact ⟨by simp [separated], fun _ _ _ h => h.elim⟩

/-- A genuine empty enclosure is sound only when there are no actual values. -/
theorem empty_cover_characterization (R : ℝ → ℝ → Prop) :
    FiniteLinearCover.Covers [] R ↔ ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z, ¬ R t z := by
  simp [FiniteLinearCover.Covers]

def varyingCover : FiniteLinearCover :=
  [parameter.sub (constantModel 2), parameter.add (constantModel 2)]
def varyingValues := PiecewiseValues (fun t => t < (1/2:ℝ))
  (fun t z => Value t t (.sub .x (.const 2)) z)
  (fun t z => Value t t (.add .x (.const 2)) z)

theorem varying_evaluated_cover : varyingCover.Covers varyingValues := by
  exact cover_select (c := .unknown) trivial
    (cover_guarded (X := parameter) (Y := parameter)
      (fun t _ => parameter_contains t) (fun t _ => parameter_contains t) rfl)
    (cover_guarded (X := parameter) (Y := parameter)
      (fun t _ => parameter_contains t) (fun t _ => parameter_contains t) rfl)

theorem varying_excludes_zero {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ¬ varyingValues t 0 := by
  apply cover_excludes_zero varying_evaluated_cover _ ht
  intro I hi
  rcases List.mem_cons.mp hi with rfl | hi
  · decide +kernel
  · rcases List.mem_singleton.mp hi with rfl
    decide +kernel

theorem varying_has_value (t : ℝ) : ∃ z, varyingValues t z := by
  by_cases h : t < (1/2:ℝ)
  · exact ⟨t - 2, Or.inl ⟨h, Value.sub Value.x (Value.const 2)⟩⟩
  · exact ⟨t + 2, Or.inr ⟨h, Value.add Value.x (Value.const 2)⟩⟩

theorem varying_reciprocal_has_value {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃ z, QuotientValues (fun _ z => z = 1) varyingValues t z := by
  obtain ⟨y, hy⟩ := varying_has_value t
  refine ⟨1/y, 1, y, rfl, hy, ?_, rfl⟩
  intro hz
  subst y
  exact varying_excludes_zero ht hy

theorem varying_reciprocal_succeeds : varyingCover.recip?.isSome := by decide +kernel

end GeneralizedIntervalArithmetic.FiniteLinearCoverExamples
