import FormatDigits

namespace GeneralizedIntervalArithmetic.Binary64Format
open FiniteFormat FormatDigits

/-- Repaired magnitude-digit parameters, not the literal source coefficient format. -/
def format : Format := ⟨2,53,-1022,1023,by decide,by decide,by decide⟩

def significand (w : Binary64.Word) : ℕ :=
  if Binary64.exponent w = 0 then Binary64.fraction w else 2^52 + Binary64.fraction w

def exponent (w : Binary64.Word) : ℤ :=
  if Binary64.exponent w = 0 then -1022 else (Binary64.exponent w : ℤ) - 1023

/-- Exact finite decoder denotation, with a separate minimum-exponent branch. -/
theorem decode_formula {w : Binary64.Word} {q : ℚ} (h : Binary64.decode w = some q) :
    q = Binary64.sign w * eval format (significand w) (exponent w) := by
  unfold Binary64.decode at h
  dsimp only at h
  split_ifs at h with bad hz he
  · cases h
    simp only [significand,exponent,hz,if_true,eval,format,shift]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, Int.reduceSub]
    ring
  · cases h
    have heq : (Binary64.exponent w:ℤ)-1023-52 = -((1075-Binary64.exponent w:ℕ):ℤ) := by omega
    simp only [significand,exponent,hz,if_false,eval,format,shift,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
    rw [heq,zpow_neg,zpow_natCast]
    ring
  · cases h
    have heq : (Binary64.exponent w:ℤ)-1023-52 = ((Binary64.exponent w-1075:ℕ):ℤ) := by omega
    simp only [significand,exponent,hz,if_false,eval,format,shift,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
    rw [heq,zpow_natCast]
    ring

/-- Every successful word supplies a valid normal-or-minimum digit presentation. -/
theorem decode_presentation {w : Binary64.Word} {q : ℚ} (h : Binary64.decode w = some q) :
    NormalOrMinimum format (significand w) (exponent w) := by
  have hn : ¬ (2^64 ≤ w ∨ Binary64.exponent w = 2047) := by
    intro hh
    have := (Binary64.no_value_iff w).mpr hh
    rw [h] at this
    contradiction
  obtain ⟨he,hf⟩ := Binary64.fields_bounded w
  unfold NormalOrMinimum Admitted significand exponent
  dsimp only [format]
  split_ifs with hz
  · norm_num at *
    omega
  · norm_num at *
    omega

/-- Complete forward finite-value bridge, including both signs and both zeros. -/
theorem decoded_repaired {w : Binary64.Word} {q : ℚ} (h : Binary64.decode w = some q) :
    Repaired format q := by
  have hp := decode_presentation h
  refine ⟨significand w,exponent w,hp.1,hp.2.1,hp.2.2.1,?_⟩
  rw [decode_formula h]
  unfold Binary64.sign
  split <;> simp

/-- The subnormal/zero branch uses the fixed minimum exponent with no hidden bit. -/
theorem subnormal_presentation {w : Binary64.Word} {q : ℚ}
    (h : Binary64.decode w = some q) (he : Binary64.exponent w = 0) :
    significand w < 2^52 ∧ exponent w = -1022 ∧
    q = Binary64.sign w * ((Binary64.fraction w:ℚ) / 2^1074) := by
  have hf := (Binary64.fields_bounded w).2
  refine ⟨by simpa [significand,he] using hf,by simp [exponent,he],?_⟩
  rw [decode_formula h]
  simp only [significand,exponent,he,if_true,eval,format,shift]
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,Int.reduceSub]
  ring

/-- Nonzero exponent words are normalized A-digit presentations. -/
theorem normal_presentation {w : Binary64.Word} {q : ℚ}
    (h : Binary64.decode w = some q) (he : Binary64.exponent w ≠ 0) :
    Normalized format (significand w) ∧ exponent w = (Binary64.exponent w:ℤ)-1023 := by
  refine ⟨⟨?_,(decode_presentation h).1⟩,by simp [exponent,he]⟩
  simp [significand,he,format]

def pack (negative : Bool) (e f : ℕ) : Binary64.Word :=
  (if negative then 2^63 else 0) + e*2^52 + f

theorem pack_fields (negative : Bool) {e f : ℕ} (he : e < 2047) (hf : f < 2^52) :
    pack negative e f < 2^64 ∧ Binary64.exponent (pack negative e f) = e ∧
      Binary64.fraction (pack negative e f) = f := by
  have hd (m : ℕ) : (m*2^52+f)/2^52=m := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num)]
    rw [Nat.div_eq_of_lt hf,zero_add]
  have hm (m : ℕ) : (m*2^52+f)%2^52=f := by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hf]
  have he' : e < 2048 := by omega
  have hmag : e*2^52+f < 2^63 := by norm_num at *; nlinarith
  cases negative
  · simp only [pack,Bool.false_eq_true,if_false,zero_add,Binary64.exponent,Binary64.fraction]
    exact ⟨hmag.trans (by norm_num),by rw [hd,Nat.mod_eq_of_lt he'],hm _⟩
  · have hp : pack true e f = (2048+e)*2^52+f := by unfold pack; norm_num; ring
    have hh : (2048+e)*2^52+f = 2^63+(e*2^52+f) := by ring
    rw [hp]
    refine ⟨?_,?_,hm _⟩
    · rw [hh]
      have := Nat.add_lt_add_left hmag (2^63)
      simpa only [show (2:ℕ)^63+2^63=2^64 by norm_num] using this
    · unfold Binary64.exponent
      rw [hd]
      omega

theorem pack_sign (negative : Bool) {e f : ℕ} (he : e < 2047) (hf : f < 2^52) :
    Binary64.sign (pack negative e f) = if negative then -1 else 1 := by
  have hmag : e*2^52+f < 2^63 := by norm_num at *; nlinarith
  unfold Binary64.sign pack
  cases negative <;> simp only [Bool.false_eq_true,if_false,if_true,zero_add]
  · exact if_pos hmag
  · rw [Nat.add_assoc]
    exact if_neg (Nat.not_lt.mpr (Nat.le_add_right _ _))

theorem pack_decode (negative : Bool) {e f : ℕ} (he : e < 2047) (hf : f < 2^52) :
    Binary64.decode (pack negative e f) = some
      ((if negative then -1 else 1) * eval format
        (if e=0 then f else 2^52+f) (if e=0 then -1022 else (e:ℤ)-1023)) := by
  have hp := pack_fields negative he hf
  obtain ⟨q,hq⟩ := Binary64.finite _ hp.1 (by rw [hp.2.1]; omega)
  rw [hq]
  congr 1
  rw [decode_formula hq,pack_sign negative he hf]
  simp only [significand,exponent,hp.2.1,hp.2.2]

/-- Every normal-or-minimum presentation has a finite raw-word representative. -/
theorem presentation_word (negative : Bool) {n : ℕ} {e : ℤ}
    (h : NormalOrMinimum format n e) :
    ∃ w, Binary64.decode w = some ((if negative then -1 else 1) * eval format n e) := by
  have hn : n < 2^53 := h.1
  have he : -1022 ≤ e ∧ e ≤ 1023 := ⟨h.2.1,h.2.2.1⟩
  have hh : 2^52 ≤ n ∨ e = -1022 := h.2.2.2
  by_cases hz : n < 2^52
  · have hem : e = -1022 := by omega
    refine ⟨pack negative 0 n,?_⟩
    simpa [hem] using pack_decode negative (e:=0) (by norm_num) hz
  · have he0 : 0 ≤ e+1023 := by omega
    have hcast : ((e+1023).toNat:ℤ) = e+1023 := Int.toNat_of_nonneg he0
    have hp : (e+1023).toNat < 2047 := by omega
    have hf : n-2^52 < 2^52 := by norm_num at hn ⊢; omega
    have hn' : 2^52+(n-2^52)=n := by omega
    have hnz : (e+1023).toNat ≠ 0 := by omega
    refine ⟨pack negative (e+1023).toNat (n-2^52),?_⟩
    have hh := pack_decode negative hp hf
    simp only [if_neg hnz,hn',hcast,add_sub_cancel_right] at hh
    exact hh

/-- Moving a leading zero into the exponent preserves the exact rational value. -/
theorem double_shift (n : ℕ) (e : ℤ) :
    eval format n (e+1) = eval format (2*n) e := by
  unfold eval
  have he : e+1-shift format = (e-shift format)+1 := by omega
  rw [he,zpow_add₀ (by norm_num [format] : (format.radix:ℚ) ≠ 0)]
  norm_num only [format,Nat.cast_ofNat,Nat.cast_mul,zpow_one]
  ring

/-- Finite normalization stops at the minimum exponent; no values are discarded. -/
theorem normalize_steps (k : ℕ) : ∀ n : ℕ, n < 2^53 → k ≤ 2045 →
    ∃ n' e', NormalOrMinimum format n' e' ∧
      eval format n (-1022+(k:ℤ)) = eval format n' e' := by
  induction k with
  | zero =>
    intro n hn _
    exact ⟨n,-1022,minimum_admitted format hn,by simp⟩
  | succ k ih =>
    intro n hn hk
    by_cases hnorm : 2^52 ≤ n
    · refine ⟨n,-1022+((k+1:ℕ):ℤ),?_,rfl⟩
      exact ⟨hn,by norm_num [format]; omega,by norm_num [format]; omega,Or.inl hnorm⟩
    · have hn2 : 2*n < 2^53 := by norm_num at hn hnorm ⊢; omega
      obtain ⟨n',e',hp,hval⟩ := ih (2*n) hn2 (by omega)
      refine ⟨n',e',hp,?_⟩
      calc
        _ = eval format n ((-1022+(k:ℤ))+1) := by congr 1; omega
        _ = eval format (2*n) (-1022+(k:ℤ)) := double_shift n _
        _ = _ := hval

theorem normalize {n : ℕ} {e : ℤ} (hn : Admitted format n)
    (he : format.minExponent ≤ e) (hf : e ≤ format.maxExponent) :
    ∃ n' e', NormalOrMinimum format n' e' ∧ eval format n e = eval format n' e' := by
  have he0 : 0 ≤ e+1022 := by change -1022 ≤ e at he; omega
  have hc : ((e+1022).toNat:ℤ)=e+1022 := Int.toNat_of_nonneg he0
  have hk : (e+1022).toNat ≤ 2045 := by change e ≤ 1023 at hf; omega
  simpa [hc] using normalize_steps (e+1022).toNat n hn hk

/-- Exact equality of finite rational denotations; no claim about encodings or hardware. -/
theorem repaired_iff_decode (q : ℚ) : Repaired format q ↔ ∃ w, Binary64.decode w = some q := by
  constructor
  · rintro ⟨n,e,hn,he,hf,hq⟩
    obtain ⟨n',e',hp,hval⟩ := normalize hn he hf
    rcases hq with rfl | rfl
    · simpa [hval] using presentation_word false hp
    · simpa [hval] using presentation_word true hp
  · rintro ⟨w,hw⟩
    exact decoded_repaired hw

/-- The repaired family is exactly the existing finite demotion target set. -/
theorem repaired_iff_binaryValues (q : ℚ) : Repaired format q ↔ q ∈ DiscreteDemotion.binaryValues := by
  rw [repaired_iff_decode,DiscreteDemotion.mem_binaryValues]
  constructor
  · rintro ⟨w,hw⟩
    refine ⟨w,?_,hw⟩
    by_contra hbad
    have hn := Binary64.out_of_range w (not_lt.mp hbad)
    rw [hw] at hn
    contradiction
  · rintro ⟨w,_,hw⟩
    exact ⟨w,hw⟩

/-- Existing mathematical directed demotion fixes every repaired finite value. -/
theorem repaired_fixed {q : ℚ} (h : Repaired format q) :
    DiscreteDemotion.down DiscreteDemotion.binaryValues ((q:ℝ):EReal) = ((q:ℝ):EReal) ∧
    DiscreteDemotion.up DiscreteDemotion.binaryValues ((q:ℝ):EReal) = ((q:ℝ):EReal) := by
  obtain ⟨w,hw⟩ := (repaired_iff_decode q).mp h
  exact DiscreteDemotion.decoded_fixed hw

end GeneralizedIntervalArithmetic.Binary64Format
