import FormatDigits

/-! Uniform separation of the literal printed formats, and normalization of the
separately labeled repaired format. No IEEE or authorial-intent claim. -/
namespace GeneralizedIntervalArithmetic.FormatNormalization
open FiniteFormat FormatDigits

theorem threshold_admitted (F : Format) : Normalized F (F.radix^(F.precision-1)) := by
  refine ⟨le_rfl,?_⟩
  have hp : 0 < F.radix^(F.precision-1) := by have := F.radix_ge_two; positivity
  have he : F.precision = (F.precision-1)+1 := by have := F.precision_pos; omega
  unfold Admitted
  conv_rhs => rw [he,pow_succ]
  exact lt_mul_of_one_lt_right hp (by have := F.radix_ge_two; omega)

/-- Every literal coefficient value is strictly below the upper-exponent unit,
even when arbitrary lower exponents and negative coefficients are admitted. -/
theorem literal_upper (F : Format) {q : ℚ} (hq : q ∈ values F) :
    q < (F.radix : ℚ)^F.maxExponent := by
  by_cases hq0 : 0 ≤ q
  · obtain ⟨n,e,hn,_,he,rfl⟩ := (literal_nonnegative F q).mp ⟨hq,hq0⟩
    exact (literal_below F hn e).trans_le
      (zpow_le_zpow_right₀ (by have := F.radix_ge_two; exact_mod_cast (show 1≤F.radix by omega)) he)
  · have hp : 0 < (F.radix : ℚ)^F.maxExponent := by have := F.radix_ge_two; positivity
    exact (lt_of_not_ge hq0).trans hp

/-- The unsigned printed digit display itself admits this positive witness. -/
theorem upper_digit_witness (F : Format) :
    Normalized F (F.radix^(F.precision-1)) ∧
    F.minExponent ≤ F.maxExponent ∧
    eval F (F.radix^(F.precision-1)) F.maxExponent = (F.radix:ℚ)^F.maxExponent ∧
    (F.radix:ℚ)^F.maxExponent ∉ values F := by
  refine ⟨threshold_admitted F,F.exponents_ordered,?_,?_⟩
  · simpa [eval] using scale_identity F F.maxExponent
  · intro h; exact (lt_irrefl _) (literal_upper F h)

theorem strict_repair (F : Format) :
    {q | q ∈ values F} ⊂ {q | Repaired F q} := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨fun _ h => literal_in_repaired F h,?_⟩
  intro h
  have hw : Repaired F ((F.radix:ℚ)^F.maxExponent) :=
    ⟨_,_,(threshold_admitted F).2,F.exponents_ordered,le_rfl,
      Or.inl (upper_digit_witness F).2.2.1.symm⟩
  have hm : (F.radix:ℚ)^F.maxExponent ∈ values F := by
    change (F.radix:ℚ)^F.maxExponent ∈ {q | q ∈ values F}
    rw [h]; exact hw
  exact (upper_digit_witness F).2.2.2 hm

/-- Moving a leading zero down one exponent preserves the exact value. -/
theorem shift_digit (F : Format) (n : ℕ) (e : ℤ) :
    eval F (n*F.radix) e = eval F n (e+1) := by
  have hb : (F.radix:ℚ) ≠ 0 := by have := F.radix_ge_two; positivity
  have he : e+1-shift F = (e-shift F)+1 := by omega
  simp [eval,Nat.cast_mul,he,zpow_add₀ hb]
  ring

theorem shifted_admitted (F : Format) {n : ℕ} (hn : n < F.radix^(F.precision-1)) :
    Admitted F (n*F.radix) := by
  have he : F.precision = (F.precision-1)+1 := by have := F.precision_pos; omega
  unfold Admitted
  conv_rhs => rw [he,pow_succ]
  exact Nat.mul_lt_mul_of_pos_right hn (by have := F.radix_ge_two; omega)

/-- A terminating induction on the distance to minimum exponent, including zero. -/
theorem normalize_distance (F : Format) (k : ℕ) : ∀ n, Admitted F n →
    F.minExponent + (k:ℤ) ≤ F.maxExponent →
    ∃ m e, NormalOrMinimum F m e ∧ eval F n (F.minExponent+(k:ℤ)) = eval F m e := by
  induction k with
  | zero =>
    intro n hn _
    exact ⟨n,F.minExponent,minimum_admitted F hn,by simp⟩
  | succ k ih =>
    intro n hn he
    by_cases ht : F.radix^(F.precision-1) ≤ n
    · exact ⟨n,F.minExponent+(k+1:ℕ),⟨hn,by omega,he,Or.inl ht⟩,rfl⟩
    · obtain ⟨m,e,hm,hv⟩ := ih (n*F.radix) (shifted_admitted F (lt_of_not_ge ht)) (by omega)
      refine ⟨m,e,hm,?_⟩
      rw [← hv,shift_digit]
      congr 1
      push_cast
      ring

theorem normalize (F : Format) {n : ℕ} {e : ℤ} (hn : Admitted F n)
    (hl : F.minExponent ≤ e) (hu : e ≤ F.maxExponent) :
    ∃ m d, NormalOrMinimum F m d ∧ eval F n e = eval F m d := by
  have he : F.minExponent+((e-F.minExponent).toNat:ℤ)=e := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  simpa only [he] using normalize_distance F (e-F.minExponent).toNat n hn (by simpa only [he] using hu)

/-- Equality of value sets, not equality or uniqueness of representations.
The external sign and minimum-exponent restriction are labeled repair choices. -/
theorem repaired_iff_normal_or_minimum (F : Format) (q : ℚ) : Repaired F q ↔
    ∃ n e, NormalOrMinimum F n e ∧ (q=eval F n e ∨ q= -eval F n e) := by
  constructor
  · rintro ⟨n,e,hn,hl,hu,hq⟩
    obtain ⟨m,d,hm,he⟩ := normalize F hn hl hu
    exact ⟨m,d,hm,by simpa only [he] using hq⟩
  · rintro ⟨n,e,hn,hq⟩
    exact ⟨n,e,hn.1,hn.2.1,hn.2.2.1,hq⟩

end GeneralizedIntervalArithmetic.FormatNormalization
