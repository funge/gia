import DigitExtraction
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Tupper §2.15.3: a mathematical floating-radix correspondence.
The explicit normalization below fixes the otherwise unspecified scale convention.
It is not a finite floating-point format or an executable exact-real oracle. -/
namespace GeneralizedIntervalArithmetic.FloatingDigits
open DigitExtraction DigitRepresentations

/-- The fractional significand has no leading zero; upper endpoint is excluded. -/
def Normalized (b : ℕ) (m : ℝ) : Prop := (b:ℝ)⁻¹ ≤ m ∧ m < 1

/-- Sign bit only; the original real value is not rounded. -/
def signed (negative : Bool) (x : ℝ) : ℝ := if negative then -x else x

theorem normalized_pos {b : ℕ} (hb : 2≤b) {m : ℝ} (hm : Normalized b m) : 0<m :=
  lt_of_lt_of_le (by positivity) hm.1

theorem positive_scale {b : ℕ} (hb : 2≤b) {x : ℝ} (hx : 0<x) :
    ∃ e : ℤ, Normalized b (x / (b:ℝ)^e) := by
  have hp : (0:ℝ)<b := by positivity
  have h1 : (1:ℝ)<b := by exact_mod_cast (show 1<b by omega)
  obtain ⟨n,hl,hu⟩ := exists_mem_Ico_zpow hx h1
  refine ⟨n+1,?_,(div_lt_one (zpow_pos hp _)).2 hu⟩
  apply (le_div_iff₀ (zpow_pos hp _)).2
  calc
    (b:ℝ)⁻¹ * (b:ℝ)^(n+1) = (b:ℝ)^n := by
      rw [zpow_add₀ (ne_of_gt hp),zpow_one]; field_simp
    _ ≤ x := hl

theorem scale_bracket {b : ℕ} (hb : 2≤b) {m : ℝ} (hm : Normalized b m) (e : ℤ) :
    (b:ℝ)^(e-1) ≤ m*(b:ℝ)^e ∧ m*(b:ℝ)^e < (b:ℝ)^e := by
  have hp : (0:ℝ)<b := by positivity
  constructor
  · have h := mul_le_mul_of_nonneg_right hm.1 (zpow_pos hp e).le
    have he : (b:ℝ)⁻¹*(b:ℝ)^e=(b:ℝ)^(e-1) := by
      rw [zpow_sub₀ (ne_of_gt hp),zpow_one]; ring
    rwa [he] at h
  · simpa using mul_lt_mul_of_pos_right hm.2 (zpow_pos hp e)

/-- The half-open normalization fixes the scale, independently of digit syntax. -/
theorem scale_unique {b : ℕ} (hb : 2≤b) {m n : ℝ}
    (hm : Normalized b m) (hn : Normalized b n) {e f : ℤ}
    (he : m*(b:ℝ)^e=n*(b:ℝ)^f) : e=f ∧ m=n := by
  have hp : (0:ℝ)<b := by positivity
  have h1 : (1:ℝ)≤b := by exact_mod_cast (show 1≤b by omega)
  have hm' := scale_bracket hb hm e
  have hn' := scale_bracket hb hn f
  have hef : e=f := by
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · have ho := zpow_le_zpow_right₀ h1 (show e≤f-1 by omega)
      rw [←he] at hn'
      linarith
    · have ho := zpow_le_zpow_right₀ h1 (show f≤e-1 by omega)
      rw [he] at hm'
      linarith
  refine ⟨hef,?_⟩
  rw [hef] at he
  exact (mul_right_cancel₀ (ne_of_gt (zpow_pos hp f))) he

/-- Every nonzero real has an ordinary canonical fractional significand,
integer radix exponent and sign. The scale choice is mathematical. -/
theorem nonzero_coverage {b : ℕ} (hb : 2≤b) {x : ℝ} (hx : x≠0) :
    ∃ negative : Bool, ∃ e : ℤ, ∃ d : ℕ→ℤ,
      Ordinary b d ∧ Canonical b d ∧ Normalized b (value d b) ∧
      x=signed negative (value d b*(b:ℝ)^e) := by
  obtain ⟨e,he⟩ := positive_scale hb (abs_pos.mpr hx)
  have hp : (0:ℝ)<b := by positivity
  have hr : |x|/(b:ℝ)^e ∈ Set.Ico (0:ℝ) 1 :=
    ⟨(normalized_pos hb he).le,he.2⟩
  have hd := extraction_exact hb hr
  refine ⟨decide (x<0),e,digits b (|x|/(b:ℝ)^e),digits_ordinary hb hr,
    extracted_canonical hb hr,by rwa [hd],?_⟩
  rw [hd,div_mul_cancel₀ _ (ne_of_gt (zpow_pos hp e))]
  by_cases hn : x<0
  · simp [signed,hn,abs_of_neg hn]
  · simp [signed,hn,abs_of_nonneg (le_of_not_gt hn)]

/-- Canonical digits remove the trailing-maximal ambiguity; normalization
separately removes the exponent ambiguity. -/
theorem digits_scale_unique {b : ℕ} (hb : 2≤b) {d c : ℕ→ℤ}
    (hd : Ordinary b d) (hc : Ordinary b c) (hcd : Canonical b d) (hcc : Canonical b c)
    (hnd : Normalized b (value d b)) (hnc : Normalized b (value c b))
    {e f : ℤ} (h : value d b*(b:ℝ)^e=value c b*(b:ℝ)^f) : e=f ∧ d=c := by
  obtain ⟨he,hv⟩ := scale_unique hb hnd hnc h
  exact ⟨he,(canonical_unique hb hd hc hcd hcc).1 hv⟩

/-- Zero is represented separately; a normalized positive significand cannot
represent it at a finite integer exponent, with either sign. -/
theorem normalized_nonzero {b : ℕ} (hb : 2≤b) {m : ℝ} (hm : Normalized b m)
    (negative : Bool) (e : ℤ) : signed negative (m*(b:ℝ)^e) ≠ 0 := by
  have hp : 0<m*(b:ℝ)^e := mul_pos (normalized_pos hb hm) (by positivity)
  cases negative <;> simp [signed,ne_of_gt hp]

theorem zero_representation (b : ℕ) : value (fun _ => 0) b=0 := by
  simp [value,term]

/-- A genuinely positive first digit, not just a bound on the decoded value. -/
theorem first_digit_pos {b : ℕ} (hb : 2≤b) {m : ℝ} (hm : Normalized b m) :
    1≤digits b m 0 := by
  have hp : (0:ℝ)<b := by positivity
  have h := mul_le_mul_of_nonneg_left hm.1 hp.le
  rw [mul_inv_cancel₀ (ne_of_gt hp)] at h
  exact Int.le_floor.mpr (by simpa [digits,remainder] using h)

/-- Positivity fixes the sign independently of the radix scale. -/
theorem signed_unique {x y : ℝ} (hx : 0<x) (hy : 0<y) {a c : Bool}
    (h : signed a x=signed c y) : a=c ∧ x=y := by
  cases a <;> cases c
  · exact ⟨rfl,h⟩
  · simp [signed] at h; linarith
  · simp [signed] at h; linarith
  · exact ⟨rfl,neg_injective h⟩

theorem normalized_representation_unique {b : ℕ} (hb : 2≤b) {d c : ℕ→ℤ}
    (hd : Ordinary b d) (hc : Ordinary b c) (hcd : Canonical b d) (hcc : Canonical b c)
    (hnd : Normalized b (value d b)) (hnc : Normalized b (value c b))
    {a z : Bool} {e f : ℤ}
    (h : signed a (value d b*(b:ℝ)^e)=signed z (value c b*(b:ℝ)^f)) :
    a=z ∧ e=f ∧ d=c := by
  have hp : (0:ℝ)<b := by positivity
  obtain ⟨hs,hv⟩ := signed_unique
    (mul_pos (normalized_pos hb hnd) (zpow_pos hp _))
    (mul_pos (normalized_pos hb hnc) (zpow_pos hp _)) h
  exact ⟨hs,digits_scale_unique hb hd hc hcd hcc hnd hnc hv⟩

/-- All reals, with a single explicitly fixed representation for zero. -/
theorem coverage (b : ℕ) (hb : 2≤b) (x : ℝ) :
    ∃ negative : Bool, ∃ e : ℤ, ∃ d : ℕ→ℤ,
      Ordinary b d ∧ Canonical b d ∧ x=signed negative (value d b*(b:ℝ)^e) ∧
      ((negative=false ∧ e=0 ∧ d=(fun _ => 0)) ∨ Normalized b (value d b)) := by
  by_cases hx : x=0
  · subst x
    refine ⟨false,0,(fun _ => 0),?_,?_,?_,Or.inl ⟨rfl,rfl,rfl⟩⟩
    · intro n; dsimp; constructor <;> omega
    · intro N; exact ⟨N,le_rfl,by dsimp; omega⟩
    · simp [zero_representation,signed]
  · obtain ⟨a,e,d,hd,hc,hn,he⟩ := nonzero_coverage hb hx
    exact ⟨a,e,d,hd,hc,he,Or.inr hn⟩

end GeneralizedIntervalArithmetic.FloatingDigits
