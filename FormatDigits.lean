import FiniteFormat
import Mathlib.Data.Nat.Digits

namespace GeneralizedIntervalArithmetic.FormatDigits
open FiniteFormat

/-- Unsigned packed A-digit magnitude; missing leading digits are zero. -/
def Admitted (F : Format) (n : ℕ) : Prop := n < F.radix ^ F.precision

def eval (F : Format) (n : ℕ) (e : ℤ) : ℚ :=
  (n : ℚ) * (F.radix : ℚ) ^ (e - shift F)

theorem eval_nonnegative (F : Format) (n : ℕ) (e : ℤ) : 0 ≤ eval F n e := by
  unfold eval
  have := F.radix_ge_two
  positivity

def Normalized (F : Format) (n : ℕ) : Prop :=
  F.radix ^ (F.precision-1) ≤ n ∧ Admitted F n

/-- Derived repaired convention, not an assertion about IEEE encodings. -/
def Repaired (F : Format) (q : ℚ) : Prop :=
  ∃ n e, Admitted F n ∧ F.minExponent ≤ e ∧ e ≤ F.maxExponent ∧
    (q = eval F n e ∨ q = -eval F n e)

theorem digit_list (F : Format) (n : ℕ) : Admitted F n ↔
    ∃ ds : List ℕ, ds.length ≤ F.precision ∧ (∀ d ∈ ds, d < F.radix) ∧
      Nat.ofDigits F.radix ds = n := by
  have hb : 1 < F.radix := by have := F.radix_ge_two; omega
  constructor
  · intro hn
    refine ⟨Nat.digits F.radix n, ?_,fun d hd => Nat.digits_lt_base hb hd,
      Nat.ofDigits_digits _ _⟩
    by_cases hz : n=0
    · simp [hz]
    · rw [Nat.digits_len _ _ hb hz]
      have := (Nat.lt_pow_iff_log_lt hb hz).mp hn
      omega
  · rintro ⟨ds,hlen,hd,rfl⟩
    exact (Nat.ofDigits_lt_base_pow_length hb hd).trans_le
      (Nat.pow_le_pow_right (by omega) hlen)

theorem scale_identity (F : Format) (e : ℤ) :
    ((F.radix : ℚ) ^ (F.precision-1)) * (F.radix : ℚ) ^ (e-shift F) =
      (F.radix : ℚ)^e := by
  have hb : (F.radix : ℚ) ≠ 0 := by have := F.radix_ge_two; positivity
  rw [← zpow_natCast, ← zpow_add₀ hb]
  congr 1
  simp [shift]

/-- Place the radix point after the leading magnitude digit. -/
theorem radix_point (F : Format) (n : ℕ) (e : ℤ) :
    eval F n e = ((n:ℚ) / (F.radix:ℚ)^(F.precision-1)) * (F.radix:ℚ)^e := by
  have hb : (F.radix:ℚ) ≠ 0 := by have := F.radix_ge_two; positivity
  unfold eval
  rw [zpow_sub₀ hb]
  simp only [shift,zpow_natCast]
  ring

theorem scale_high (F : Format) (e : ℤ) :
    ((F.radix:ℚ)^F.precision) * (F.radix:ℚ)^(e-shift F) = (F.radix:ℚ)^(e+1) := by
  have hb : (F.radix:ℚ) ≠ 0 := by have := F.radix_ge_two; positivity
  have he : F.precision=(F.precision-1)+1 := by have := F.precision_pos; omega
  have hp : (F.radix:ℚ)^F.precision = (F.radix:ℚ)^(F.precision-1)*(F.radix:ℚ) := by
    conv_lhs => rw [he]
    rw [pow_succ]
  calc
    _ = (((F.radix:ℚ)^(F.precision-1)) * (F.radix:ℚ)^(e-shift F)) * F.radix := by rw [hp]; ring
    _ = (F.radix:ℚ)^e * F.radix := by rw [scale_identity]
    _ = _ := by rw [zpow_add₀ hb]; simp

/-- Exact normalized binade at the fixed exponent, not a continuous image claim. -/
theorem normalized_iff (F : Format) (n : ℕ) (e : ℤ) : Normalized F n ↔
    (F.radix:ℚ)^e ≤ eval F n e ∧ eval F n e < (F.radix:ℚ)^(e+1) := by
  have hp : 0 < (F.radix:ℚ)^(e-shift F) := by have := F.radix_ge_two; positivity
  rw [← scale_identity F e, ← scale_high F e]
  unfold eval Normalized Admitted
  rw [mul_le_mul_right hp, mul_lt_mul_right hp]
  norm_cast

/-- Same-exponent lower leading digit is exactly the normalization threshold. -/
theorem normalized_lower (F : Format) {n : ℕ} (hn : Normalized F n) (e : ℤ) :
    (F.radix : ℚ)^e ≤ eval F n e := by
  rw [← scale_identity F e]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast hn.1
  · have := F.radix_ge_two; positivity

/-- Every normalized presentation has magnitude at least the minimum-exponent unit. -/
theorem normalized_minimum (F : Format) {n : ℕ} (hn : Normalized F n)
    {e : ℤ} (he : F.minExponent ≤ e) :
    (F.radix : ℚ)^F.minExponent ≤ eval F n e :=
  (zpow_le_zpow_right₀ (by have := F.radix_ge_two; norm_cast; omega) he).trans
    (normalized_lower F hn e)

/-- Literal nonnegative coefficients lie below the normalization threshold at the same exponent. -/
theorem literal_below (F : Format) {n : ℕ}
    (hn : n < F.radix ^ (F.precision-1)) (e : ℤ) :
    eval F n e < (F.radix : ℚ)^e := by
  rw [← scale_identity F e]
  apply mul_lt_mul_of_pos_right
  · exact_mod_cast hn
  · have := F.radix_ge_two; positivity

/-- Exact reindexing of the nonnegative part of the printed coefficient formula. -/
theorem literal_nonnegative (F : Format) (q : ℚ) :
    (q ∈ values F ∧ 0 ≤ q) ↔
    ∃ n e, n < F.radix^(F.precision-1) ∧ F.minExponent ≤ e ∧ e ≤ F.maxExponent ∧
      q = eval F n e := by
  constructor
  · rintro ⟨hq,hq0⟩
    obtain ⟨a,c,ha,hb,hc,hd,rfl⟩ := (mem_values F q).mp hq
    have hp : 0 < (F.radix : ℚ)^c := by have := F.radix_ge_two; positivity
    have ha0 : 0 ≤ a := by
      have : (0:ℚ) ≤ a := (mul_nonneg_iff_of_pos_right hp).mp hq0
      exact_mod_cast this
    refine ⟨a.toNat,c+shift F,?_,hc,hd,?_⟩
    · exact_mod_cast (show (a.toNat : ℤ) < (F.radix : ℤ)^(F.precision-1) by simpa [Int.toNat_of_nonneg ha0] using hb)
    · have hnat : (a.toNat : ℚ) = (a : ℚ) := by exact_mod_cast (Int.toNat_of_nonneg ha0)
      simp [eval,value,hnat]
  · rintro ⟨n,e,hn,he,hf,rfl⟩
    refine ⟨(mem_values F _).mpr ⟨n,e-shift F,?_,?_,by omega,by omega,by simp [eval,value]⟩,?_⟩
    · have hb : 0 < bound F := by unfold bound; have := F.radix_ge_two; positivity
      have : (0:ℤ) ≤ n := by positivity
      omega
    · unfold bound; exact_mod_cast hn
    · unfold eval; have := F.radix_ge_two; positivity

/-- The most significant (zero-padded) digit is nonzero exactly at the threshold. -/
theorem leading_nonzero (F : Format) (n : ℕ) :
    n / F.radix^(F.precision-1) ≠ 0 ↔ F.radix^(F.precision-1) ≤ n := by
  have hp : 0 < F.radix^(F.precision-1) := by have := F.radix_ge_two; positivity
  simp only [ne_eq, Nat.div_eq_zero_iff, ne_of_gt hp, false_or, not_lt]

theorem leading_bounded (F : Format) {n : ℕ} (hn : Admitted F n) :
    n / F.radix^(F.precision-1) < F.radix := by
  have hp : 0 < F.radix^(F.precision-1) := by have := F.radix_ge_two; positivity
  apply (Nat.div_lt_iff_lt_mul hp).mpr
  have he : F.precision = (F.precision-1)+1 := by have := F.precision_pos; omega
  have hpow : F.radix ^ F.precision = F.radix^(F.precision-1) * F.radix := by
    conv_lhs => rw [he]
    rw [pow_succ]
  simpa only [Admitted, hpow, Nat.mul_comm] using hn

/-- A chosen repair: A magnitude digits and an external sign correspond exactly
 to the coefficient bound b^A, leaving the source exponent shift unchanged. -/
theorem repaired_coefficients (F : Format) (q : ℚ) : Repaired F q ↔
    ∃ a c : ℤ, -(F.radix:ℤ)^F.precision < a ∧ a < (F.radix:ℤ)^F.precision ∧
      F.minExponent ≤ c+shift F ∧ c+shift F ≤ F.maxExponent ∧ q=value F a c := by
  have hp : (0:ℤ) < (F.radix:ℤ)^F.precision := by have := F.radix_ge_two; positivity
  constructor
  · rintro ⟨n,e,hn,he,hf,hq⟩
    have hn' : (n:ℤ) < (F.radix:ℤ)^F.precision := by exact_mod_cast hn
    rcases hq with rfl | rfl
    · exact ⟨n,e-shift F,by omega,hn',by omega,by omega,by simp [eval,value]⟩
    · exact ⟨-(n:ℤ),e-shift F,by omega,by omega,by omega,by omega,by simp [eval,value]⟩
  · rintro ⟨a,c,ha,hb,hc,hd,rfl⟩
    by_cases hz : 0≤a
    · have hn : (a.toNat:ℤ)=a := Int.toNat_of_nonneg hz
      have hnq : (a.toNat:ℚ)=(a:ℚ) := by exact_mod_cast hn
      exact ⟨a.toNat,c+shift F,by unfold Admitted; exact_mod_cast (hn ▸ hb),hc,hd,
        Or.inl (by simp [value,eval,hnq])⟩
    · have hn : ((-a).toNat:ℤ) = -a := Int.toNat_of_nonneg (by omega)
      have hnq : ((-a).toNat:ℚ)=-(a:ℚ) := by exact_mod_cast hn
      refine ⟨(-a).toNat,c+shift F,?_,hc,hd,Or.inr ?_⟩
      · unfold Admitted
        have : ((-a).toNat:ℤ) < (F.radix:ℤ)^F.precision := by omega
        exact_mod_cast this
      · simp [value,eval,hnq]

/-- Every literal signed presentation fits the repaired signed magnitude range. -/
theorem literal_in_repaired (F : Format) {q : ℚ} (hq : q ∈ values F) : Repaired F q := by
  obtain ⟨a,c,ha,hb,hc,hd,hq⟩ := (mem_values F q).mp hq
  apply (repaired_coefficients F q).mpr
  have hpow : bound F ≤ (F.radix:ℤ)^F.precision := by
    unfold bound
    exact pow_le_pow_right₀ (by have := F.radix_ge_two; exact_mod_cast (show 1≤F.radix by omega)) (by omega)
  exact ⟨a,c,by omega,lt_of_lt_of_le hb hpow,hc,hd,hq⟩

/-- This is an explicitly chosen minimum-exponent convention, not an IEEE claim. -/
def NormalOrMinimum (F : Format) (n : ℕ) (e : ℤ) : Prop :=
  Admitted F n ∧ F.minExponent ≤ e ∧ e ≤ F.maxExponent ∧
    (F.radix^(F.precision-1) ≤ n ∨ e=F.minExponent)

theorem minimum_admitted (F : Format) {n : ℕ} (hn : Admitted F n) :
    NormalOrMinimum F n F.minExponent :=
  ⟨hn,le_rfl,F.exponents_ordered,Or.inr rfl⟩

theorem minimum_not_normalizable (F : Format) {n : ℕ}
    (hn : n < F.radix^(F.precision-1)) :
    ¬ ∃ k e, Normalized F k ∧ F.minExponent ≤ e ∧ eval F n F.minExponent = eval F k e := by
  rintro ⟨k,e,hk,he,heq⟩
  have hl := literal_below F hn F.minExponent
  have hu := normalized_minimum F hk he
  rw [heq] at hl
  exact (not_lt_of_ge hu) hl

end GeneralizedIntervalArithmetic.FormatDigits
