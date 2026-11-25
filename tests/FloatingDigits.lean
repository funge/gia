import FloatingDigits
import AuditPolicy
namespace GeneralizedIntervalArithmetic.FloatingDigitsChecks
open FloatingDigits DigitExtraction DigitRepresentations

example (x : ℝ) : ∃ negative : Bool, ∃ e : ℤ, ∃ d : ℕ→ℤ,
    Ordinary 10 d ∧ Canonical 10 d ∧ x=signed negative (value d 10*(10:ℝ)^e) ∧
    ((negative=false ∧ e=0 ∧ d=(fun _ => 0)) ∨ Normalized 10 (value d 10)) :=
  coverage 10 (by norm_num) x

theorem large_positive : Normalized 10 (1/10) ∧
    (1000:ℝ)=signed false ((1/10)*(10:ℝ)^(4:ℤ)) := by norm_num [Normalized,signed]

theorem small_negative : Normalized 10 (1/10) ∧
    (-1/1000:ℝ)=signed true ((1/10)*(10:ℝ)^(-2:ℤ)) := by norm_num [Normalized,signed]

theorem boundary_flags : Normalized 10 (1/10) ∧ ¬Normalized 10 1 ∧
    ¬Normalized 10 0 := by norm_num [Normalized]

theorem zero_sign_ambiguity : signed true 0=signed false 0 := by norm_num [signed]

theorem nonzero_first : digits 10 (1/10) 0=1 := by norm_num [digits,remainder]

theorem insufficient_scale_convention :
    ∃ d c : ℕ→ℤ, Ordinary 10 d ∧ Canonical 10 d ∧
      Ordinary 10 c ∧ Canonical 10 c ∧
      value d 10*(10:ℝ)^(1:ℤ)=1 ∧ value c 10*(10:ℝ)^(2:ℤ)=1 ∧
      Normalized 10 (value d 10) ∧ ¬Normalized 10 (value c 10) := by
  have h1 : (1/10:ℝ) ∈ Set.Ico 0 1 := by norm_num
  have h2 : (1/100:ℝ) ∈ Set.Ico 0 1 := by norm_num
  refine ⟨digits 10 (1/10),digits 10 (1/100),digits_ordinary (by norm_num) h1,
    extracted_canonical (by norm_num) h1,digits_ordinary (by norm_num) h2,
    extracted_canonical (by norm_num) h2,?_⟩
  rw [extraction_exact (by norm_num) h1,extraction_exact (by norm_num) h2]
  norm_num [Normalized]

theorem scale_is_forced {m : ℝ} (hm : Normalized 10 m) {e : ℤ}
    (h : m*(10:ℝ)^e=1) : e=1 ∧ m=1/10 := by
  apply scale_unique (by norm_num) hm (show Normalized 10 (1/10) by norm_num [Normalized])
  norm_num
  exact h

theorem maximal_tail_excluded : ¬Canonical 10 (fun _ => 9) := by
  intro h
  obtain ⟨n,_,hn⟩ := h 0
  norm_num at hn

#audit_namespace GeneralizedIntervalArithmetic.FloatingDigitsChecks
end GeneralizedIntervalArithmetic.FloatingDigitsChecks
