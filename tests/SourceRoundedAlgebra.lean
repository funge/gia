import SourceRoundedAlgebra
import AuditPolicy
set_option maxRecDepth 10000
namespace GeneralizedIntervalArithmetic.SourceRoundedAlgebraChecks
open SourceRoundedAlgebra FiniteFormat DirectedOperationAlgebra

/-- Finite test table only; deliberately not a general rounding algorithm. -/
def probe (m : Mode) (x : ℚ) : ℚ :=
  if x=102 then smallResult m else if x= -99999 then innerResult m else x

theorem probe_exact (m : Mode) {q : ℚ} (hq : q∈values literal)
    (h1 : q≠102) (h2 : q≠ -99999) : Rounds (values literal) m q (probe m q) := by
  simpa [probe,h1,h2] using rounds_exact hq m

theorem probe_small (m : Mode) : Rounds (values literal) m 102 (probe m 102) := by
  simpa [probe] using small_accepted m
theorem probe_inner (m : Mode) : Rounds (values literal) m (-99999) (probe m (-99999)) := by
  simpa [probe] using inner_accepted m

theorem multiplication_all_modes (m : Mode) :
    probe m (probe m (3*34)*(1/2)) ≠ probe m (3*probe m (34*(1/2))) := by
  apply multiplication_nonassoc probe m (probe_small m)
  all_goals apply probe_exact m (literal_constants (by simp)) <;> norm_num

theorem all_243_mixed_laws (m₁ m₂ m₃ m₄ m₅ : Mode) :
    probe m₂ (2*probe m₁ (51+(-50))) ≠
      probe m₅ (probe m₃ (2*51)+probe m₄ (2*(-50))) := by
  apply mixed_distributivity probe m₁ m₂ m₃ m₄ m₅ (probe_small m₃)
  intro m q hq
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  all_goals apply probe_exact m (literal_constants (by simp)) <;> norm_num

theorem printed_rows_checked (m : Mode) :
    probe m (probe m (100000+(-100000))+1)=1 ∧
    probe m (100000+probe m ((-100000)+1))=rightResult m := by
  apply printed_reassociation probe m (probe_inner m)
  intro q hq
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  all_goals apply probe_exact m (literal_constants (by simp)) <;> norm_num

theorem printed_down_not_10000 :
    probe .down (100000+probe .down ((-100000)+1))=0 ∧
    probe .down (100000+probe .down ((-100000)+1))≠10000 := by
  have h := (printed_rows_checked .down).2
  norm_num [rightResult] at h
  norm_num only
  exact ⟨h,by rw [h]; norm_num⟩

theorem repaired_right_up : Rounded (values repairedIndex) (100000 + (-99900)) 100 100 := by
  have h : (100:ℚ)∈values repairedIndex := by
    convert repaired_scaled 100 0 (by norm_num) using 1; norm_num
  convert exact_representable h using 1; norm_num

theorem repaired_right_down : Rounded (values repairedIndex) (100000 + (-100000)) 0 0 := by
  have h : (0:ℚ)∈values repairedIndex := by
    convert repaired_scaled 0 0 (by norm_num) using 1; norm_num
  convert exact_representable h using 1; norm_num

theorem printed_decimal_conflict :
    Rounded (values literal) 1001 1000 1100 ∧
    Rounded (values repairedIndex) 1001 1000 1010 ∧
    ¬∃l,Rounded (values literal) 1001 l 1010 :=
  ⟨decimal_literal,decimal_repaired,literal_up_not_printed⟩

theorem addition_operands_represented :
    (100000:ℚ)∈values literal ∧ (-100000:ℚ)∈values literal ∧ (1:ℚ)∈values literal :=
  ⟨literal_constants (by simp),neg_member literal (literal_constants (by simp)),literal_constants (by simp)⟩
theorem multiplication_operands_represented :
    (3:ℚ)∈values literal ∧ (34:ℚ)∈values literal ∧ (1/2:ℚ)∈values literal :=
  ⟨literal_constants (by simp),literal_constants (by simp),literal_constants (by simp)⟩

theorem tie_not_chosen : Nearest ({0,2}:Finset ℚ) 1 0 ∧ Nearest ({0,2}:Finset ℚ) 1 2 := by
  norm_num [Nearest]

theorem new_row_old_unchanged (x : ℝ) :
    sourceAddObservation .posInf (.finite x)=some .posInf ∧
    ExceptionalComparisons.addObservation .posInf (.finite x)=none := ⟨rfl,rfl⟩
theorem exceptional_equality_distinct :
    sourceAddObservation .posInf (.finite 1)=some .posInf ∧
    ExceptionalComparisons.observe .eq .posInf .posInf=some false := ⟨rfl,rfl⟩
theorem no_lambda_guess : sourceAddObservation .posInf .undefined=none := rfl

end GeneralizedIntervalArithmetic.SourceRoundedAlgebraChecks
#audit_namespace GeneralizedIntervalArithmetic.SourceRoundedAlgebraChecks
