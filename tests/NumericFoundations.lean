import NumericFoundations
import AuditPolicy
namespace GeneralizedIntervalArithmetic.NumericFoundationsChecks
open NumericFoundations

theorem cast_chain : ((((-3 : ℤ) : ℚ) : ℝ) : ℂ) = -3 := by norm_num
theorem guarded_nonzero : PartialRealArithmetic.divRel (3 : ℝ) 2 (3/2) := by
  norm_num [PartialRealArithmetic.divRel, PartialRealArithmetic.divDefined, PartialRealArithmetic.div]
theorem zero_not_defined : ¬ PartialRealArithmetic.divRel (3 : ℝ) 0 0 := by
  simp [PartialRealArithmetic.divRel, PartialRealArithmetic.divDefined]
theorem rational_perfect_square : ∃ q : ℚ, q^2 = 9/4 := ⟨3/2, by norm_num⟩
theorem irrational_obstruction : ¬ ∃ q : ℚ, q^2 = 2 := no_rational_root_two
theorem real_zero : ∃ z : ℝ, 0 ≤ z ∧ z^2 = 0 := (real_root_domain 0).2 le_rfl
theorem domain_changes : (¬ ∃ z : ℝ, 0 ≤ z ∧ z^2 = -1) ∧
    (∃ w : ℂ, w^2 = -1) := by
  constructor
  · rw [real_root_domain]; norm_num
  · exact ⟨Complex.I, complex_negative_root⟩
theorem negative_not_finite_zero :
    ExceptionalComparisons.sqrtObservation (.finite (-1)) ≠ some (.finite 0) := by
  intro h
  have hh := (root_observation_graph (-1) 0).1 h
  norm_num at hh
theorem square_inverse_sign : Real.sqrt ((-2 : ℝ)^2) = 2 ∧
    Real.sqrt ((-2 : ℝ)^2) ≠ -2 := by rw [Real.sqrt_sq_eq_abs]; norm_num
theorem complex_zero : complexRoot 0 ^ 2 = 0 := complex_root_square 0
theorem complex_nonreal : ∃ w : ℂ, w^2 = Complex.I := complex_root_total _
theorem real_representation_exists (x : ℝ) :
    ∃ u : ℕ → ℚ, SequenceRepresentations.Represents u x := rational_sequence_exists x
theorem rational_constant : SequenceRepresentations.Represents (fun _ => (1/2:ℚ)) (1/2) := by
  simpa using rational_constant_representation (1/2)
end GeneralizedIntervalArithmetic.NumericFoundationsChecks
#audit_namespace GeneralizedIntervalArithmetic.NumericFoundationsChecks
