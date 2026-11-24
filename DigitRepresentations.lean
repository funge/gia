import SequenceRepresentations

/-! Tupper §§2.15.3 and 2.15.6: ordinary and signed bounded digit sums.
Index n denotes the source digit d_(n+1), never the integer part. -/
namespace GeneralizedIntervalArithmetic.DigitRepresentations
open Filter
open scoped Topology BigOperators

noncomputable def term (d : ℕ → ℤ) (b : ℕ) (n : ℕ) : ℝ :=
  (d n : ℝ) * ((b:ℝ)⁻¹)^(n+1)
noncomputable def value (d : ℕ → ℤ) (b : ℕ) : ℝ := ∑' n, term d b n

def partialSum (d : ℕ → ℤ) (b N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, (d n : ℚ) * ((b:ℚ)⁻¹)^(n+1)

theorem geometric_majorant {b : ℕ} (hb : 2≤b) :
    HasSum (fun n:ℕ => ((b:ℝ)-1) * ((b:ℝ)⁻¹)^(n+1)) 1 := by
  have hbr : (1:ℝ)<b := by exact_mod_cast (show 1<b by omega)
  have hr0 : 0≤(b:ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hr1 : (b:ℝ)⁻¹<1 := (inv_lt_one₀ (by positivity)).mpr hbr
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (((b:ℝ)-1)*(b:ℝ)⁻¹)
  convert h using 1
  · ext n; rw [pow_succ]; ring
  · rw [← div_eq_mul_inv, eq_div_iff (sub_ne_zero.mpr (ne_of_gt hr1))]
    field_simp

theorem term_bound {d : ℕ → ℤ} {b : ℕ} (hb : 2≤b)
    (hd : ∀n, |d n| ≤ (b:ℤ)-1) (n : ℕ) :
    ‖term d b n‖ ≤ ((b:ℝ)-1) * ((b:ℝ)⁻¹)^(n+1) := by
  have hd' : |(d n:ℝ)| ≤ (b:ℝ)-1 := by exact_mod_cast hd n
  simpa [term, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0≤(b:ℝ)⁻¹)]
    using mul_le_mul_of_nonneg_right hd' (pow_nonneg (by positivity : 0≤(b:ℝ)⁻¹) (n+1))

theorem summable {d : ℕ → ℤ} {b : ℕ} (hb : 2≤b)
    (hd : ∀n, |d n| ≤ (b:ℤ)-1) : Summable (term d b) :=
  Summable.of_norm_bounded _ (geometric_majorant hb).summable (term_bound hb hd)

/-- Both ordinary and redundant bounded digits define an actual real value. -/
theorem signed_range {d : ℕ → ℤ} {b : ℕ} (hb : 2≤b)
    (hd : ∀n, |d n| ≤ (b:ℤ)-1) : value d b ∈ Set.Icc (-1) 1 := by
  have h := (summable hb hd).hasSum.norm_le_of_bounded (geometric_majorant hb) (term_bound hb hd)
  exact abs_le.mp (by simpa [value,Real.norm_eq_abs] using h)

theorem ordinary_range {d : ℕ → ℤ} {b : ℕ} (hb : 2≤b)
    (hd : ∀n, 0≤d n ∧ d n < b) : value d b ∈ Set.Icc 0 1 := by
  have hh : ∀n, |d n|≤(b:ℤ)-1 := fun n => by
    have hn := hd n
    rw [abs_of_nonneg hn.1]
    omega
  refine ⟨?_,(signed_range hb hh).2⟩
  exact tsum_nonneg (fun n => mul_nonneg (by exact_mod_cast (hd n).1) (by positivity))

/-- Rational partial sums supply the concrete sequence representation. -/
theorem partial_represents {d : ℕ → ℤ} {b : ℕ} (hb : 2≤b)
    (hd : ∀n, |d n| ≤ (b:ℤ)-1) :
    SequenceRepresentations.Represents (partialSum d b) (value d b) := by
  simpa [SequenceRepresentations.Represents,partialSum,value,term] using
    (summable hb hd).hasSum.tendsto_sum_nat

/-- A derived effective truncation bound for bounded digits, unlike a general
converging sequence with no supplied modulus. No digit extraction is constructed. -/
theorem truncation_bound {d : ℕ → ℤ} {b : ℕ} (hb : 2≤b)
    (hd : ∀n, |d n| ≤ (b:ℤ)-1) (N : ℕ) :
    |value d b - (partialSum d b N : ℝ)| ≤ ((b:ℝ)⁻¹)^N := by
  have hg : HasSum (fun n:ℕ => ((b:ℝ)-1)*((b:ℝ)⁻¹)^(n+N+1)) (((b:ℝ)⁻¹)^N) := by
    convert (geometric_majorant hb).mul_left (((b:ℝ)⁻¹)^N) using 1
    · funext n; simp only [pow_add,pow_one]; ring
    · ring
  have ht := tsum_of_norm_bounded hg (fun n => term_bound hb hd (n+N))
  have hp : (∑ n ∈ Finset.range N, term d b n) = (partialSum d b N : ℝ) := by
    simp [partialSum,term]
  unfold value
  rw [← (summable hb hd).sum_add_tsum_nat_add N,hp]
  simpa [Real.norm_eq_abs] using ht

/-- The source sum identity is prior to carrying. Output digits need not be valid. -/
theorem addition {d e : ℕ → ℤ} {b : ℕ} (hb : 2≤b)
    (hd : ∀n, |d n| ≤ (b:ℤ)-1) (he : ∀n, |e n| ≤ (b:ℤ)-1) :
    value (fun n => d n + e n) b = value d b + value e b := by
  have h : term (fun n=>d n+e n) b = fun n=>term d b n + term e b n := by
    funext n; simp [term,add_mul]
  unfold value
  rw [h]
  exact (summable hb hd).tsum_add (summable hb he)

/-- Negation of a signed expansion preserves the represented value's sign. -/
theorem negation (d : ℕ → ℤ) (b : ℕ) :
    value (fun n=> -d n) b = -value d b := by
  simp [value,term,tsum_neg]

/-- Maximal ordinary digits represent 1; negatives are a signed representation of -1. -/
theorem maximal_digits {b : ℕ} (hb : 2≤b) : value (fun _ => (b:ℤ)-1) b = 1 := by
  simpa [value,term] using (geometric_majorant hb).tsum_eq

/-- The source strict signed-digit condition, translated to integral digits. -/
theorem signed_condition {d : ℕ → ℤ} {b : ℕ} :
    (∀n, -(b:ℤ)<d n ∧ d n<b) ↔ (∀n, |d n|≤(b:ℤ)-1) := by
  simp only [abs_le]
  constructor <;> intro h n <;> have hn := h n <;> omega

def terminating (n : ℕ) : ℤ := if n=0 then 1 else 0
def repeating (b n : ℕ) : ℤ := if n=0 then 0 else (b:ℤ)-1

theorem terminating_value (b : ℕ) : value terminating b = (b:ℝ)⁻¹ := by
  unfold value
  rw [tsum_eq_single 0 (fun n hn => by simp [term,terminating,hn])]
  simp [term,terminating]

/-- Infinite expansion equality, not a finite decimal approximation. -/
theorem repeating_value {b : ℕ} (hb : 2≤b) : value (repeating b) b = (b:ℝ)⁻¹ := by
  have h := (geometric_majorant hb).mul_left ((b:ℝ)⁻¹)
  have ht : HasSum (fun n => term (repeating b) b (n+1)) ((b:ℝ)⁻¹) := by
    convert h using 1
    · funext n
      simp [term,repeating,pow_succ]
      ring
    · ring
  have ha : HasSum (term (repeating b) b) ((b:ℝ)⁻¹) :=
    (hasSum_nat_add_iff' 1).mp (by simpa [term,repeating] using ht)
  exact ha.tsum_eq

end GeneralizedIntervalArithmetic.DigitRepresentations
