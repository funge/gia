import DigitRepresentations
import AuditPolicy
namespace GeneralizedIntervalArithmetic.DigitRepresentationsChecks
open DigitRepresentations

theorem decimal_duplicate : terminating ≠ repeating 10 ∧
    value terminating 10 = 1/10 ∧ value (repeating 10) 10 = 1/10 := by
  refine ⟨?_,by simpa using terminating_value 10,by simpa using repeating_value (by norm_num : 2≤10)⟩
  intro h
  have hh := congrFun h 0
  norm_num [terminating,repeating] at hh

theorem zero_digits : value (fun _=>0) 10 = 0 := by simp [value,term]

theorem signed_negative : value (fun _=>(-9:ℤ)) 10 = -1 := by
  have h := negation (fun _=>(9:ℤ)) 10
  have hm := maximal_digits (by norm_num : 2≤10)
  norm_num at hm
  simpa [hm] using h

theorem signed_input_range :
    value (fun n=>if n%2=0 then (9:ℤ) else -9) 10 ∈ Set.Icc (-1) 1 := by
  apply signed_range (by norm_num)
  intro n; split_ifs <;> norm_num

theorem ordinary_boundary : value (fun _=>(9:ℤ)) 10=1 ∧
    value terminating 10 ∈ Set.Icc 0 1 := by
  refine ⟨by simpa using maximal_digits (by norm_num : 2≤10),?_⟩
  apply ordinary_range (by norm_num)
  intro n; simp only [terminating]; split_ifs <;> norm_num

/-- The uncarried sum is correct but the summed digits are not base-2 digits. -/
theorem carrying_required :
    value (fun _=>(2:ℤ)) 2 = 2 ∧ ¬ (0≤(2:ℤ) ∧ (2:ℤ)<2) := by
  have h := addition (d:=fun _=>1) (e:=fun _=>1) (b:=2)
    (by norm_num) (by norm_num) (by norm_num)
  have hm : value (fun _=>(1:ℤ)) 2=1 := by simpa using maximal_digits (by norm_num : 2≤2)
  exact ⟨by simpa only [hm,show (1:ℤ)+1=2 by norm_num,show (1:ℝ)+1=2 by norm_num] using h,by norm_num⟩

theorem rational_partial_sums :
    SequenceRepresentations.Represents (partialSum (repeating 10) 10) (1/10) := by
  have hd : ∀n, |repeating 10 n|≤(10:ℤ)-1 := by
    intro n; simp only [repeating]; split_ifs <;> norm_num
  have h := partial_represents (by norm_num : 2≤10) hd
  have hv : value (repeating 10) 10 = 1/10 := by simpa using repeating_value (by norm_num : 2≤10)
  rwa [hv] at h

/-- Excluded base 1 is genuinely unsafe: the constant positive term does not sum. -/
theorem base_one_not_summable : ¬ Summable (term (fun _=>1) 1) := by
  have he : term (fun _=>1) 1 = fun _:ℕ => (1:ℝ) := by funext n; norm_num [term]
  rw [he,summable_const_iff]
  norm_num

theorem binary_truncation : partialSum (fun _=>1) 2 4 = 15/16 ∧
    |value (fun _=>1) 2 - (partialSum (fun _=>1) 2 4 : ℝ)| = 1/16 := by
  have hp : partialSum (fun _=>1) 2 4 = 15/16 := by
    norm_num [partialSum,Finset.sum_range_succ]
  refine ⟨hp,?_⟩
  rw [hp]
  have hm : value (fun _=>(1:ℤ)) 2=1 := by simpa using maximal_digits (by norm_num : 2≤2)
  rw [hm]
  norm_num

theorem signed_zero_not_unique :
    (fun n=>terminating n + -repeating 2 n) ≠ (fun _=>0) ∧
    value (fun n=>terminating n + -repeating 2 n) 2 = 0 := by
  have ht : ∀n,|terminating n|≤(2:ℤ)-1 := by
    intro n; simp only [terminating]; split_ifs <;> norm_num
  have hr : ∀n,|-repeating 2 n|≤(2:ℤ)-1 := by
    intro n; simp only [repeating]; split_ifs <;> norm_num
  refine ⟨?_,?_⟩
  · intro h
    have hh := congrFun h 0
    norm_num [terminating,repeating] at hh
  · rw [addition (by norm_num) ht hr,negation,terminating_value,
      repeating_value (by norm_num : 2≤2)]
    ring

end GeneralizedIntervalArithmetic.DigitRepresentationsChecks
#audit_namespace GeneralizedIntervalArithmetic.DigitRepresentationsChecks
