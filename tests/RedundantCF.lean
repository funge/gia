import RedundantCF
import AuditPolicy
namespace GeneralizedIntervalArithmetic.RedundantCFChecks
open RedundantCF
open Filter
open scoped Topology

def twos (n : ℕ) : ℤ := if n=0 then 0 else 2

theorem twos_admissible : Admissible twos := by
  constructor
  · intro n; norm_num [twos]
  · intro n _; norm_num [twos]

theorem twos_converges : ∃! x, Represents twos x := unique_value twos_admissible

theorem negative_twos_converges : ∃! x, Represents (fun n => -twos n) x :=
  unique_value (admissible_neg twos_admissible)

theorem negative_twos_prefix : trunc (fun n => -twos n) 0 3 = -5/12 := by
  norm_num [trunc,InfiniteSimpleCF.trunc,twos]

def alternating (n : ℕ) : ℤ := if n=0 then 0 else if n%2=0 then 3 else -3

theorem alternating_admissible : Admissible alternating := by
  constructor
  · intro n; simp only [alternating,Nat.add_eq_zero_iff,one_ne_zero,and_false,↓reduceIte]
    split_ifs <;> norm_num
  · intro n; simp only [alternating,Nat.add_eq_zero_iff,one_ne_zero,two_ne_zero,and_false,↓reduceIte]
    split_ifs <;> norm_num

theorem sign_changes_converge : ∃! x, Represents alternating x :=
  unique_value alternating_admissible

theorem sign_change_prefix : trunc alternating 0 3 = -8/21 := by
  norm_num [trunc,InfiniteSimpleCF.trunc,alternating]

theorem all_divisors_defined (n k : ℕ) : trunc alternating (n+1) k ≠ 0 :=
  trunc_tail_nonzero alternating_admissible n k

theorem error_control (v : ℕ → ℝ) (hv : InfiniteSimpleCF.SuffixLimits alternating v) :
    |v 0-(trunc alternating 0 2:ℝ)| ≤ 16/81 := by
  convert limit_error alternating_admissible hv 0 2 using 1; norm_num

/-- The adjacent-sign condition is substantive, not a cosmetic restriction. -/
theorem forbidden_flip :
    ¬Admissible (fun n => if n=1 then (2:ℤ) else -2) ∧
    InfiniteSimpleCF.fraction (fun n => if n=1 then (2:ℤ) else -2) 0 2 > 1/2 := by
  constructor
  · intro h
    have := h.2 0 (by norm_num)
    norm_num at this
  · norm_num [InfiniteSimpleCF.fraction]

/-- Two literal admissible finite presentations denote the same rational. -/
theorem finite_nonuniqueness : FiniteTail [3] ∧ FiniteTail [2,1] ∧
    ContinuedFractionConversion.finiteValue 0 [3] = (1/3:ℚ) ∧
    ContinuedFractionConversion.finiteValue 0 [2,1] = (1/3:ℚ) ∧
    ([3] : List ℤ) ≠ [2,1] := by
  norm_num [FiniteTail,ContinuedFractionConversion.finiteValue_cons,
    ContinuedFractionConversion.finiteValue_nil]

/-- Printed finite syntax alone does not certify all real divisions defined.
This is not an assertion that totalized 1/0 is a source-valid real operation. -/
theorem terminal_zero_control : FiniteTail [3,0] ∧
    ContinuedFractionConversion.finiteValue 0 [] = (0:ℚ) := by
  norm_num [FiniteTail,ContinuedFractionConversion.finiteValue_nil]

theorem excluded_last_negative_two : ¬FiniteTail [3,-2] := by
  norm_num [FiniteTail]

theorem positive_overlap (x : ℝ) (hx : Represents twos x) :
    GenContFract.of x = InfiniteSimpleCF.presentation twos ∧
      (¬∃q:ℚ, x=(q:ℝ)) ∧
      Tendsto (InfiniteSimpleCF.presentation twos).convs atTop (𝓝 x) :=
  positive_recovery twos_admissible (by simp [twos]) (by intro n; simp [twos]) hx

#eval (List.range 4).map (trunc alternating 0)
#audit_namespace GeneralizedIntervalArithmetic.RedundantCFChecks
end GeneralizedIntervalArithmetic.RedundantCFChecks
