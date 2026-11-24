import FiniteEquality
import AuditPolicy

namespace GeneralizedIntervalArithmetic.FiniteEqualityChecks
open StrictComparison BooleanComposition DomainProjections DomainConstraints FiniteEquality

def a : QInterval := ⟨1,3,by norm_num⟩
def b : QInterval := ⟨2,4,by norm_num⟩
def touch : QInterval := ⟨3,4,by norm_num⟩
def away : QInterval := ⟨4,6,by norm_num⟩
def signed : QInterval := ⟨-1,1,by norm_num⟩
def closed : QInterval := ⟨0,1,by norm_num⟩

theorem source_equal_examples : compareEQ a b = .both ∧
    compareEQ (point 3) (point 3) = .trueOnly := by decide

theorem disjoint_and_touching : compareEQ a away = .falseOnly ∧
    compareNE a away = .trueOnly ∧ compareEQ a touch = .both := by decide

theorem touching_witnesses : true ∈ eqOutcomes a touch ∧ false ∈ eqOutcomes a touch := by
  constructor
  · rw [eq_true_attainable]; norm_num [a,touch]
  · rw [eq_false_attainable]; norm_num [a,touch]

theorem identical_marginals_are_not_same_witness :
    compareEQ signed signed = .both ∧ (∀ x : ℝ, x = x) ∧ (∀ x : ℝ, ¬ x ≠ x) := by
  exact ⟨by decide,fun _ => rfl,fun _ => not_not.mpr rfl⟩

theorem all_finite_comparisons :
    StrictComparison.compare a away = .trueOnly ∧
    StrictComparison.compare away a = .falseOnly ∧
    compareLE a away = .trueOnly ∧ compareLE away a = .falseOnly ∧
    compareEQ a away = .falseOnly ∧ compareNE a away = .trueOnly := by decide

theorem nonzero_boundary_cases :
    nonzero (point 0) = .falseOnly ∧ nonzero closed = .both ∧
    nonzero signed = .both ∧ nonzero a = .trueOnly ∧
    nonzero (point (-1)) = .trueOnly := by decide

theorem exact_nonzero_crossing :
    (nonzero signed).values = numericImage nzPredicate signed := nonzero_exact _

theorem zero_and_nonzero_attained :
    false ∈ numericImage nzPredicate signed ∧ true ∈ numericImage nzPredicate signed := by
  exact ⟨⟨0,by norm_num [signed,QInterval.Contains],by simp [nzPredicate]⟩,
    ⟨1,by norm_num [signed,QInterval.Contains],by simp [nzPredicate]⟩⟩

theorem zero_only_no_reciprocal : ¬ ∃ z : ℝ, True ∧ (0 : ℝ) ≠ 0 ∧ z = 1 / 0 := by simp

theorem nonzero_with_external_hole :
    ((exactDomain (fun (_ : Unit) => False)).inter
      (domain (fun _ => nonzero a))).Compatible ()
        (∃ z : ℝ, False ∧ (2 : ℝ) ≠ 0 ∧ z = 1 / 2) := by
  apply reciprocal_constraint_compatible (fun _ => a) _ () False 2
  · exact ⟨id,id⟩
  · intro h; exact False.elim h

theorem touching_reciprocal_guard (x : ℝ) (hx : closed.Contains x) :
    ((exactDomain (fun (_ : Unit) => True)).inter
      (domain (fun _ => nonzero closed))).Compatible ()
        (∃ z : ℝ, True ∧ x ≠ 0 ∧ z = 1 / x) := by
  exact reciprocal_constraint_compatible (fun _ => closed) _ () True x ⟨id,id⟩ (fun _ => hx)

/-- Different encodings: positive x is represented as nonnegative y=x-1
on this supplied interval. This is an actual witness transport, not relabeling. -/
theorem different_encoding_transport :
    Refines (domain (fun (_ : Unit) => above 0 a))
      (domain (fun _ => atLeast 0 (⟨0,2,by norm_num⟩ : QInterval))) := by
  apply reencode_refines (fun _ => a) (fun _ => (⟨0,2,by norm_num⟩ : QInterval))
    (gtPredicate 0) (gePredicate 0) (above 0) (atLeast 0) (above_exact 0)
  · intro I y hy
    rw [atLeast_exact]
    exact ⟨y,hy,rfl⟩
  · intro p x hx
    have hx1 : (1 : ℝ) ≤ x := by simpa [a] using hx.1
    have hx3 : x ≤ (3 : ℝ) := by simpa [a] using hx.2
    refine ⟨x-1, ?_, ?_⟩
    · constructor <;> norm_num <;> linarith
    · have hp : (0 : ℝ) < x := by linarith
      have hq : (0 : ℝ) ≤ x-1 := by linarith
      simp [gePredicate,gtPredicate,hp,hq]

/-- Just changing classification predicates on the same numeric interval fails. -/
theorem encoding_match_is_necessary :
    ¬ (above 0 (point 0)).Refines (atLeast 0 (point 0)) := by
  norm_num [above,atLeast,compareLE,StrictComparison.compare,point,neg,refines_iff]
  decide

end GeneralizedIntervalArithmetic.FiniteEqualityChecks
#audit_namespace GeneralizedIntervalArithmetic.FiniteEqualityChecks
