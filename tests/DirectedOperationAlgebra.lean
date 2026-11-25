import DirectedOperationAlgebra
import AuditPolicy
namespace GeneralizedIntervalArithmetic.DirectedOperationAlgebraChecks
open DirectedOperationAlgebra

def digits : Finset ℚ := {-4,-2,-1,0,1,2,4}
theorem round_three : Rounded digits 3 2 4 := by
  apply (rounded_iff_extremal _ _ _ _).2
  norm_num [digits]
theorem round_one : Rounded digits 1 1 1 := by simpa using exact_representable (D:=digits) (q:=1) (by norm_num [digits])
theorem round_two : Rounded digits 2 2 2 := by simpa using exact_representable (D:=digits) (q:=2) (by norm_num [digits])
theorem round_zero : Rounded digits 0 0 0 := by simpa using exact_representable (D:=digits) (q:=0) (by norm_num [digits])

/-- Same represented inputs; all intermediate exact results remain in range.
This is a small finite-family control, not the printed decimal-format example. -/
theorem down_nonassociative :
    Rounded digits (2+1) 2 4 ∧ Rounded digits (2 + (-1)) 1 1 ∧
    Rounded digits (1 + (-1)) 0 0 ∧ Rounded digits (2+0) 2 2 ∧ (1:ℚ)≠2 := by
  norm_num only at *
  exact ⟨round_three,round_one,round_zero,round_two,by norm_num⟩
theorem up_nonassociative :
    Rounded digits (2+1) 2 4 ∧ Rounded digits (4 + (-1)) 2 4 ∧
    Rounded digits (1 + (-1)) 0 0 ∧ Rounded digits (2+0) 2 2 ∧ (4:ℚ)≠2 := by
  norm_num only at *
  exact ⟨round_three,round_three,round_zero,round_two,by norm_num⟩

theorem zero_division : ¬∃l u,
    Operation digits (fun p z => PartialRealArithmetic.divRel p.1 p.2 z) ((1:ℝ),0) l u := by
  rw [division_domain]; simp

theorem nonzero_but_out_of_range : ¬∃l u,
    Operation digits (fun p z => PartialRealArithmetic.divRel p.1 p.2 z) ((10:ℝ),1) l u := by
  rw [division_domain]
  norm_num [InRange,digits]

theorem successful_division : ∃l u,
    Operation digits (fun p z => PartialRealArithmetic.divRel p.1 p.2 z) ((6:ℝ),2) l u := by
  exact ⟨2,4,3,by norm_num [PartialRealArithmetic.divRel,PartialRealArithmetic.divDefined,
    PartialRealArithmetic.div],round_three⟩

theorem loose_is_not_optimal : ¬Rounded digits 3 1 4 := by
  intro h
  have hh := rounded_unique h round_three
  norm_num at hh

theorem containing_is_not_attaining : (5/2:ℝ) ∈ Set.Icc (2:ℝ) 4 ∧ (5/2:ℝ)≠3 := by norm_num

theorem empty_family_rejects (x : ℝ) : ¬∃l u,Rounded ∅ x l u := by
  rintro ⟨l,u,h⟩
  exact Finset.not_mem_empty l h.1

end GeneralizedIntervalArithmetic.DirectedOperationAlgebraChecks
#audit_namespace GeneralizedIntervalArithmetic.DirectedOperationAlgebraChecks
