import DigitExtraction
import AuditPolicy
namespace GeneralizedIntervalArithmetic.DigitExtractionChecks
open DigitExtraction DigitRepresentations

theorem tenth_digits : digits 10 (1/10) 0 = 1 ∧
    (∀n, digits 10 (1/10) (1+n)=0) := by
  constructor
  · norm_num [digits,remainder]
  · apply terminating_tail
    norm_num [remainder,Int.fract]

theorem sixth_prefix : digits 10 (1/6) 0 = 1 ∧ digits 10 (1/6) 1 = 6 := by
  norm_num [digits,remainder,Int.fract]

theorem negative_integer_part : ⌊(-1/4:ℝ)⌋ = (-1:ℤ) ∧
    digits 10 (Int.fract (-1/4)) 0=7 ∧ digits 10 (Int.fract (-1/4)) 1=5 := by
  norm_num [digits,remainder,Int.fract]

theorem arbitrary_base_recovery (b : ℕ) (hb : 2≤b) (x : ℝ) (hx : x∈Set.Ico 0 1) :
    Ordinary b (digits b x) ∧ Canonical b (digits b x) ∧ value (digits b x) b=x :=
  ⟨digits_ordinary hb hx,extracted_canonical hb hx,extraction_exact hb hx⟩

theorem fraction_one_not_canonical (d : ℕ→ℤ) (hd : Ordinary 10 d)
    (hc : Canonical 10 d) : value d 10 ≠ 1 := by
  exact ne_of_lt (canonical_range (by norm_num) hd hc).2

theorem integer_one : (1:ℝ) = (1:ℤ)+value (digits 10 0) 10 := by
  rw [extraction_exact (by norm_num) (by norm_num : (0:ℝ)∈Set.Ico 0 1)]
  norm_num

theorem maximal_tail_excluded : ¬ Canonical 10 (fun _ => (9:ℤ)) := by
  simp [Canonical]

theorem zero_canonical : Canonical 10 (fun _ => (0:ℤ)) := by
  intro N; exact ⟨N,le_rfl,by norm_num⟩

theorem terminating_canonical : Canonical 10 terminating := by
  intro N
  exact ⟨N+1,by omega,by simp [terminating]⟩

theorem repeating_not_canonical : ¬ Canonical 10 (repeating 10) := by
  intro h
  obtain ⟨n,hn,hd⟩ := h 1
  have hne : n≠0 := by omega
  norm_num [repeating,hne] at hd

theorem duplicate_is_real : value terminating 10 = value (repeating 10) 10 ∧
    terminating ≠ repeating 10 := by
  constructor
  · rw [terminating_value,repeating_value (by norm_num)]
  · intro h
    have := congrFun h 0
    norm_num [terminating,repeating] at this

/-- Unrestricted floating-place representations have a further ambiguity not
settled by fixing a fractional digit tail. -/
theorem place_ambiguity : (10:ℝ)*(1/10) = 100*(1/100) ∧ (10:ℝ)≠100 := by norm_num

/-- Invalid alphabets are outside the reconstruction theorem. -/
theorem invalid_digit : ¬Ordinary 2 (fun _ => (2:ℤ)) := by simp [Ordinary]

theorem real_representation_unique (a c : ℤ) (d e : ℕ→ℤ)
    (hd : Ordinary 10 d) (he : Ordinary 10 e) (hc : Canonical 10 d) (hf : Canonical 10 e)
    (h : (a:ℝ)+value d 10=(c:ℝ)+value e 10) : a=c ∧ d=e :=
  (representation_unique (by norm_num) a c hd he hc hf).1 h

end GeneralizedIntervalArithmetic.DigitExtractionChecks
#audit_namespace GeneralizedIntervalArithmetic.DigitExtractionChecks
