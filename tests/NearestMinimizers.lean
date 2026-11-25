import NearestMinimizers
import AuditPolicy
namespace GeneralizedIntervalArithmetic.NearestMinimizersChecks
open NearestMinimizers SourceRoundedAlgebra DirectedOperationAlgebra FiniteFormat

theorem real_input_existence : ∃q,NearestReal ({0,2}:Finset ℚ) (Real.sqrt 2) q :=
  (exists_iff _ _).2 (by simp)

theorem midpoint_both : NearestReal ({0,2}:Finset ℚ) 1 0 ∧ NearestReal ({0,2}:Finset ℚ) 1 2 := by
  apply (tie_iff _ _ _ _ (by norm_num)).2
  norm_num

theorem midpoint_not_unique : ¬∃!q,NearestReal ({0,2}:Finset ℚ) 1 q := by
  apply (nonunique_iff_midpoint_gap _ _ (by simp)).2
  refine ⟨0,2,by norm_num,?_⟩
  norm_num

theorem midpoint_only_two {q : ℚ} (h : NearestReal ({0,2}:Finset ℚ) 1 q) : q=0 ∨ q=2 :=
  tied_only_two (by norm_num) midpoint_both.1 midpoint_both.2 h

theorem equal_distances_not_enough : |(1:ℝ)-0|=|1-2| ∧
    ¬NearestReal ({0,1,2}:Finset ℚ) 1 0 := by
  constructor
  · norm_num
  · intro h
    have hh := h.2 1 (by simp)
    norm_num at hh

theorem singleton_unique : ∃!q,NearestReal ({2}:Finset ℚ) 2 q := by
  refine ⟨2,?_,fun q h => exact_unique (by simp) h⟩
  simp [NearestReal]

theorem empty_no_minimizer (x : ℝ) : ¬∃q,NearestReal ∅ x q := by rw [exists_iff]; simp

/-- Mathematical finite minimization outside range does not specify overflow. -/
theorem outside_range : NearestReal ({0,2}:Finset ℚ) 10 2 ∧
    ¬DirectedOperationAlgebra.InRange ({0,2}:Finset ℚ) 10 := by norm_num [NearestReal,DirectedOperationAlgebra.InRange]

theorem rational_bridge : NearestReal ({0,2}:Finset ℚ) (1:ℚ) 0 ↔
    SourceRoundedAlgebra.Nearest ({0,2}:Finset ℚ) 1 0 := rational_agreement _ _ _

theorem both_inverse_fail (m : Mode) : tiny≠0 ∧ tiny∈values literal ∧ tiny∈values repairedIndex ∧
    (∀q∈values literal,¬Rounds (values literal) m (tiny*q) 1) ∧
    (∀q∈values repairedIndex,¬Rounds (values repairedIndex) m (tiny*q) 1) :=
  ⟨tiny_members.2.2,tiny_members.1,tiny_members.2.1,
    fun _ h => literal_no_inverse m h,fun _ h => repaired_no_inverse m h⟩

theorem some_inverse_exists (m : Mode) :
    (2:ℚ)∈values literal ∧ (1/2:ℚ)∈values literal ∧ Rounds (values literal) m (2*(1/2)) 1 := by
  refine ⟨literal_constants (by simp),literal_constants (by simp),?_⟩
  convert rounds_exact (literal_constants (q:=1) (by simp)) m using 1; norm_num

theorem nonzero_scope_control (m : Mode) (q : ℚ) (hq : q∈values unitFormat) (hn : q≠0) :
    Rounds (values unitFormat) m (q*q) 1 := unit_format_nonzero_inverses m hq hn

theorem zero_still_not_invertible (m : Mode) (q : ℚ) :
    ¬Rounds (values unitFormat) m (0*q) 1 :=
  zero_no_inverse ((unit_format_values 0).2 (by simp)) m q

end GeneralizedIntervalArithmetic.NearestMinimizersChecks
#audit_namespace GeneralizedIntervalArithmetic.NearestMinimizersChecks
