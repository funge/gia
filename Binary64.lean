import SplitPi

namespace GeneralizedIntervalArithmetic.Binary64

/-- An unsigned raw-word input; `decode` rejects values outside 64 bits.
Using Nat avoids implicit modular wrapping of out-of-range literals. -/
abbrev Word := Nat

def exponent (w : Word) : Nat := w / 2^52 % 2048
def fraction (w : Word) : Nat := w % 2^52
def sign (w : Word) : ℚ := if w < 2^63 then 1 else -1

/-- Finite IEEE binary64 value as an exact rational. Both zeros map to zero;
infinities and all NaN payloads have no rational value. -/
def decode (w : Word) : Option ℚ :=
  let e := exponent w
  let f : ℚ := fraction w
  if w ≥ 2^64 ∨ e = 2047 then none
  else if e = 0 then some (sign w * f / 2^1074)
  else if e ≤ 1075 then some (sign w * (2^52+f) / 2^(1075-e))
  else some (sign w * (2^52+f) * 2^(e-1075))

noncomputable def real (w : Word) : Option ℝ := (decode w).map (fun q => (q:ℝ))

theorem nonfinite (w : Word) (h : exponent w = 2047) : decode w = none := by
  simp [decode,h]

theorem finite (w : Word) (hw : w < 2^64) (h : exponent w ≠ 2047) : ∃ q, decode w = some q := by
  simp only [decode,h,not_le_of_gt hw,false_or,ite_false]
  split <;> (try split) <;> exact ⟨_,rfl⟩

theorem out_of_range (w : Word) (h : 2^64 ≤ w) : decode w = none := by
  simp only [decode, if_pos (Or.inl h)]

theorem no_value_iff (w : Word) : decode w = none ↔ 2^64 ≤ w ∨ exponent w = 2047 := by
  constructor
  · intro hn
    by_contra h
    push_neg at h
    obtain ⟨q,hq⟩ := finite w (by simpa using h.1) h.2
    rw [hq] at hn
    cases hn
  · rintro (h | h)
    · exact out_of_range w h
    · exact nonfinite w h

theorem fields_bounded (w : Word) : exponent w < 2048 ∧ fraction w < 2^52 := by
  exact ⟨Nat.mod_lt _ (by norm_num),Nat.mod_lt _ (by norm_num)⟩

theorem pi_lower : decode 0x400921fb54442d18 = some (7074237752028440 / 2251799813685248) := by
  norm_num [decode,exponent,fraction,sign]
theorem pi_upper : decode 0x400921fb54442d19 = some (7074237752028441 / 2251799813685248) := by
  norm_num [decode,exponent,fraction,sign]
theorem tail_lower : decode 0x3ca1a60d3bc55bea = some (2483825185828341 / 20282409603651670423947251286016) := by
  norm_num [decode,exponent,fraction,sign]
theorem tail_upper : decode 0x3ca1a66bae498e34 = some (1242014004962189 / 10141204801825835211973625643008) := by
  norm_num [decode,exponent,fraction,sign]

theorem pi_contains : HardwareAddition.Contains real
    (⟨0x400921fb54442d18,0x400921fb54442d19⟩ : HardwareAddition.Bounds Word) Real.pi := by
  apply HardwarePi.decoded_contains
  · simp [real,pi_lower,HardwarePi.lower]
  · simp [real,pi_upper,HardwarePi.upper]

theorem tail_contains : HardwareAddition.Contains real
    (⟨0x3ca1a60d3bc55bea,0x3ca1a66bae498e34⟩ : HardwareAddition.Bounds Word)
    (Real.pi-HardwarePi.lower) := by
  apply HardwarePi.tail_contains
  · simp [real,tail_lower,HardwarePi.tailLower]
  · simp [real,tail_upper,HardwarePi.tailUpper]

end GeneralizedIntervalArithmetic.Binary64
