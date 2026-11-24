import ExceptionalComparisons
import AuditPolicy

namespace GeneralizedIntervalArithmetic.ExceptionalComparisonsChecks
open ExceptionalComparisons

theorem finite_controls :
    observe .lt (.finite (-1)) (.finite 0) = some true ∧
    observe .lt (.finite 0) (.finite 0) = some false ∧
    observe .eq (.finite 0) (.finite 0) = some true ∧
    observe .eq (.finite 0) (.finite 1) = some false := by
  norm_num [observe,finiteMeaning]

theorem undefined_is_a_known_false (op : Op) (v : ExceptionalComparisons.Value) :
    observe op .undefined v = some false ∧ observe op v .undefined = some false :=
  ⟨undefined_left op v,undefined_right op v⟩

theorem both_signed_infinity_controls :
    observe .lt .posInf .posInf = some false ∧
    observe .eq .posInf .posInf = some false ∧
    observe .lt .negInf .negInf = some false ∧
    observe .eq .negInf .negInf = some false := ⟨rfl,rfl,rfl,rfl⟩

theorem unmodeled_is_not_false : observe .lt .negInf .posInf = none ∧
    observe .lt .negInf .posInf ≠ some false := by simp [observe]

theorem no_totality_claim (op : Op) (x : ℝ) :
    observe op .negInf (.finite x) = none ∧
    observe op (.finite x) .negInf = none ∧
    observe op .posInf (.finite x) = none ∧
    observe op (.finite x) .posInf = none ∧
    observe op .negInf .posInf = none ∧
    observe op .posInf .negInf = none := mixed_unmodeled op x

theorem ordinary_trichotomy_cannot_transfer :
    ¬ (observe .lt .posInf .posInf = some true ∨
      observe .eq .posInf .posInf = some true ∨
      observe .lt .posInf .posInf = some true) := by simp [observe]

theorem structural_equality_survives : (ExceptionalComparisons.Value.undefined = ExceptionalComparisons.Value.undefined) ∧
    observe .eq .undefined .undefined = some false := ⟨rfl,rfl⟩

theorem bound_equality_survives : ((⊤ : EReal) = ⊤) ∧
    observe .eq .posInf .posInf = some false := ⟨rfl,rfl⟩

theorem bound_lt_on_known_case : (false : Bool) =
    (by classical exact decide ((⊤ : EReal) < ⊤)) :=
  strict_bound_agreement (a := .posInf) (b := .posInf) rfl rfl rfl

theorem finite_membership_boundary :
    (0:ℝ) ∈ ExtendedImageHull.interval 0 1 ∧
    observe .lt (.finite 0) (.finite 0) = some false ∧
    observe .lt (.finite 1) (.finite 0) = some false := by
  norm_num [ExtendedImageHull.interval,observe,finiteMeaning]

theorem negated_tests_need_a_finite_value :
    observe .lt .undefined (.finite 0) = some false ∧
    observe .lt (.finite 1) .undefined = some false ∧
    bound .undefined = none := undefined_passes_negated_tests 0 1

/-- Missing table rows do not deny the separate mathematical ordering. -/
theorem mathematical_bounds_are_not_the_table : (⊥ : EReal) < ⊤ ∧
    observe .lt .negInf .posInf = none := ⟨bot_lt_top,rfl⟩

theorem source_addition_table :
    addObservation (.finite (-3)) .posInf = some .posInf ∧
    addObservation .posInf .posInf = some .posInf ∧
    addObservation .negInf .posInf = none := ⟨rfl,rfl,rfl⟩

theorem source_root_table :
    sqrtObservation (.finite (-1)) = some .undefined ∧
    sqrtObservation (.finite 0) = some (.finite 0) ∧
    sqrtObservation (.finite 4) = some (.finite 2) := by
  norm_num [sqrtObservation]
  rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem finite_add_control : addObservation (.finite 2) (.finite 3) = some (.finite 5) := by
  norm_num [addObservation]

theorem specified_undefined_not_unmodeled :
    sqrtObservation (.finite (-1)) ≠ none ∧ sqrtObservation .posInf = none := by
  rw [sqrt_negative _ (by norm_num)]
  exact ⟨by simp,rfl⟩

theorem no_assumed_lambda_propagation (v : ExceptionalComparisons.Value) :
    addObservation .undefined v = none ∧ addObservation v .undefined = none := by
  cases v <;> exact ⟨rfl,rfl⟩

theorem result_equation_not_numerical_equality :
    addObservation .posInf .posInf = some .posInf ∧
    observe .eq .posInf .posInf = some false := ⟨rfl,rfl⟩

theorem negative_root_cannot_supply_bound :
    sqrtObservation (.finite (-1)) = some .undefined ∧ bound .undefined = none ∧
    Real.sqrt (-1) = 0 := by
  exact ⟨sqrt_negative _ (by norm_num),rfl,Real.sqrt_eq_zero_of_nonpos (by norm_num)⟩

theorem five_finite_equal :
    observe .lt (.finite 0) (.finite 0) = some false ∧
    observe .le (.finite 0) (.finite 0) = some true ∧
    observe .eq (.finite 0) (.finite 0) = some true ∧
    observe .ge (.finite 0) (.finite 0) = some true ∧
    observe .gt (.finite 0) (.finite 0) = some false := by
  norm_num [observe, finiteMeaning]

theorem finite_strict_and_nonstrict :
    observe .le (.finite (-1)) (.finite 2) = some true ∧
    observe .ge (.finite (-1)) (.finite 2) = some false ∧
    observe .gt (.finite 2) (.finite (-1)) = some true := by
  norm_num [observe, finiteMeaning]

theorem no_exceptional_reflexivity (op : Op) :
    observe op .posInf .posInf = some false ∧
    observe op .negInf .negInf = some false ∧
    observe op .undefined .undefined = some false := ⟨rfl, rfl, rfl⟩

theorem le_not_negated_gt_at_lambda :
    observe .le .undefined (.finite 0) = some false ∧
    (observe .gt .undefined (.finite 0)).map Bool.not = some true := ⟨rfl, rfl⟩

theorem le_not_bound_order :
    (⊤ : EReal) ≤ ⊤ ∧ observe .le .posInf .posInf = some false := ⟨le_rfl, rfl⟩

theorem derived_missing_stays_missing :
    observe .le .negInf (.finite 0) = none ∧
    observedOr (observe .lt .negInf (.finite 0))
      (observe .eq .negInf (.finite 0)) = none ∧
    observe .ge .posInf .negInf = none := ⟨rfl, rfl, rfl⟩

theorem converse_is_not_complement :
    observe .gt (.finite 0) (.finite 0) = observe .lt (.finite 0) (.finite 0) ∧
    observe .gt (.finite 0) (.finite 0) ≠
      (observe .lt (.finite 0) (.finite 0)).map Bool.not := by
  norm_num [observe, finiteMeaning]

end GeneralizedIntervalArithmetic.ExceptionalComparisonsChecks
#audit_namespace GeneralizedIntervalArithmetic.ExceptionalComparisonsChecks
