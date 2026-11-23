import WordTwoCorner

namespace GeneralizedIntervalArithmetic.Binary64Key

def signBit : Nat := 2^63
def magnitude (w : Nat) : Nat := w % signBit
def finite (w : Nat) : Bool := decide (w < 2^64 ∧ magnitude w < 0x7ff0000000000000)
def key (w : Nat) : Nat := if w < signBit then signBit + magnitude w else signBit - magnitude w

theorem exponent_magnitude (w : Nat) : Binary64.exponent w = magnitude w / 2^52 := by
  unfold Binary64.exponent magnitude signBit
  omega

theorem finite_iff (w : Nat) : finite w = true ↔ ∃ q, Binary64.decode w = some q := by
  rw [show (∃ q, Binary64.decode w = some q) ↔ Binary64.decode w ≠ none by
    cases Binary64.decode w <;> simp]
  rw [ne_eq, Binary64.no_value_iff]
  simp only [finite, decide_eq_true_eq]
  rw [exponent_magnitude]
  have hm : magnitude w < 2^63 := Nat.mod_lt _ (by norm_num [signBit])
  norm_num at *
  omega

theorem key_fits (w : Nat) (h : finite w = true) : key w < 2^64 := by
  simp only [finite, decide_eq_true_eq] at h
  unfold key signBit
  split <;> norm_num at * <;> omega

theorem key_zero : key 0 = signBit ∧ key signBit = signBit := by
  norm_num [key,magnitude,signBit]

def magnitude64 (w : UInt64) : UInt64 := w % 0x8000000000000000

def finite64 (w : UInt64) : Bool := decide (magnitude64 w < 0x7ff0000000000000)

def key64 (w : UInt64) : UInt64 :=
  if w < 0x8000000000000000 then 0x8000000000000000 + magnitude64 w
  else 0x8000000000000000 - magnitude64 w

theorem magnitude64_eq (w : UInt64) : (magnitude64 w).toNat = magnitude w.toNat := by
  simp [magnitude64,magnitude,signBit]

theorem finite64_eq (w : UInt64) : finite64 w = finite w.toNat := by
  have hw := w.toNat_lt_size
  simp only [finite64, UInt64.lt_iff_toNat_lt, magnitude64_eq, UInt64.toNat_ofNat]
  norm_num [finite,signBit,UInt64.size] at *
  simp [hw]

theorem key64_eq (w : UInt64) : (key64 w).toNat = key w.toNat := by
  have hm : magnitude w.toNat < 2^63 := Nat.mod_lt _ (by norm_num [signBit])
  have hs : (0x8000000000000000 : UInt64).toNat = 2^63 := rfl
  have hm64 : magnitude64 w ≤ (0x8000000000000000 : UInt64) := by
    rw [UInt64.le_iff_toNat_le, magnitude64_eq]
    rw [hs]
    omega
  unfold key64 key
  simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat]
  norm_num [signBit]
  split
  · simp only [UInt64.toNat_add, UInt64.toNat_ofNat, magnitude64_eq]
    norm_num
    omega
  · rw [UInt64.toNat_sub_of_le _ _ hm64, magnitude64_eq]
    rw [hs]
    norm_num

theorem finite64_decodes (w : UInt64) : finite64 w = true ↔
    ∃ q, Binary64.decode w.toNat = some q := by
  rw [finite64_eq,finite_iff]

theorem key64_le (u v : UInt64) : key64 u ≤ key64 v ↔ key u.toNat ≤ key v.toNat := by
  rw [UInt64.le_iff_toNat_le, key64_eq, key64_eq]

theorem key64_lt (u v : UInt64) : key64 u < key64 v ↔ key u.toNat < key v.toNat := by
  rw [UInt64.lt_iff_toNat_lt, key64_eq, key64_eq]

theorem key64_equal (u v : UInt64) : key64 u = key64 v ↔ key u.toNat = key v.toNat := by
  rw [← UInt64.toNat_inj, key64_eq, key64_eq]

/-- Reject oversized Nat input before conversion; never silently wrap. -/
def checkedKey (w : Nat) : Option UInt64 :=
  if w < 2^64 then
    let u := UInt64.ofNat w
    if finite64 u then some (key64 u) else none
  else none

theorem checkedKey_spec (w : Nat) : (checkedKey w).map UInt64.toNat =
    if finite w then some (key w) else none := by
  by_cases hw : w < 2^64
  · have hu : (UInt64.ofNat w).toNat = w := by
      simpa [UInt64.size] using UInt64.toNat_ofNat_of_lt' hw
    simp only [checkedKey,if_pos hw,finite64_eq,hu]
    cases hf : finite w
    · rfl
    · change some ((key64 (UInt64.ofNat w)).toNat) = some (key w)
      rw [key64_eq,hu]
  · have hf : finite w = false := by
      apply decide_eq_false
      intro h
      exact hw h.1
    simp only [checkedKey,if_neg hw,hf,Bool.false_eq_true,if_false]
    rfl

theorem checkedKey_available (w : Nat) : (checkedKey w).isSome = true ↔
    ∃ q, Binary64.decode w = some q := by
  have h := checkedKey_spec w
  have hi := congrArg Option.isSome h
  simp only [Option.isSome_map] at hi
  rw [← finite_iff]
  cases hf : finite w <;> simp_all

theorem nonnegative_order {u v : Nat} (hu : u < signBit) (hv : v < signBit) :
    key u ≤ key v ↔ u ≤ v := by
  simp [key,hu,hv,magnitude,Nat.mod_eq_of_lt hu,Nat.mod_eq_of_lt hv]

theorem negative_order {u v : Nat}
    (hu : signBit ≤ u) (hu' : u < 2^64)
    (hv : signBit ≤ v) (hv' : v < 2^64) : key u ≤ key v ↔ v ≤ u := by
  have hmu : magnitude u < signBit := Nat.mod_lt _ (by norm_num [signBit])
  have hmv : magnitude v < signBit := Nat.mod_lt _ (by norm_num [signBit])
  simp only [key,not_lt_of_ge hu,not_lt_of_ge hv,ite_false]
  unfold magnitude signBit at *
  omega

/-- Unsigned finite significands measured in minimum-subnormal units. -/
def units (e f : Nat) : Nat := if e = 0 then f else (2^52+f)*2^(e-1)

theorem units_upper {e f : Nat} (hf : f < 2^52) : units e f < 2^52 * 2^e := by
  by_cases he : e = 0
  · simpa [units,he] using hf
  · have hpow : 2^e = 2^(e-1)*2 := by
      rw [← pow_succ]
      congr 1
      omega
    have hp : 0 < 2^(e-1) := pow_pos (by omega) _
    simp only [units,if_neg he]
    rw [hpow]
    nlinarith

theorem units_lower {e f : Nat} (he : 0 < e) : 2^52 * 2^(e-1) ≤ units e f := by
  simp only [units,if_neg (by omega : e ≠ 0)]
  exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

theorem units_strict {e f e' f' : Nat} (hf : f < 2^52)
    (h : e < e' ∨ (e = e' ∧ f < f')) : units e f < units e' f' := by
  rcases h with h | ⟨rfl,h⟩
  · have hpow : (2:Nat)^e ≤ 2^(e'-1) :=
      pow_le_pow_right' (by omega) (by omega)
    have hlo := units_lower (f := f') (by omega : 0 < e')
    have hhi := units_upper (e := e) hf
    nlinarith
  · by_cases he : e = 0
    · simpa [units,he] using h
    · have hp : 0 < 2^(e-1) := pow_pos (by omega) _
      simp only [units,if_neg he]
      exact Nat.mul_lt_mul_of_pos_right (by omega) hp

/-- Within and across binades, unsigned raw magnitude orders the integer units. -/
theorem magnitude_units_strict {u v : Nat} (h : u < v) :
    units (u / 2^52) (u % 2^52) < units (v / 2^52) (v % 2^52) := by
  apply units_strict (Nat.mod_lt _ (by norm_num))
  have hu := Nat.mod_add_div u (2^52)
  have hv := Nat.mod_add_div v (2^52)
  have hum := Nat.mod_lt u (by norm_num : 0 < 2^52)
  have hvm := Nat.mod_lt v (by norm_num : 0 < 2^52)
  omega


theorem decode_scaled {w : Nat} {q : ℚ} (h : Binary64.decode w = some q) :
    q * (2:ℚ)^1074 = Binary64.sign w * (units (Binary64.exponent w) (Binary64.fraction w) : ℚ) := by
  unfold Binary64.decode at h
  dsimp only at h
  split_ifs at h with bad hz he
  · cases h
    simp [units,hz]
  · cases h
    have hp : (2:ℚ)^1074 = 2^(1075-Binary64.exponent w) * 2^(Binary64.exponent w-1) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [units,if_neg hz,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat]
    rw [hp]
    field_simp; ring
  · cases h
    have hp : (2:ℚ)^(Binary64.exponent w-1075) * 2^1074 = 2^(Binary64.exponent w-1) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [units,if_neg hz,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat]
    rw [mul_assoc, hp]; ring


def unsignedUnits (m : Nat) : Nat := units (m / 2^52) (m % 2^52)

theorem unsigned_strict : StrictMono unsignedUnits := fun _ _ h => magnitude_units_strict h

theorem unsigned_zero : unsignedUnits 0 = 0 := by simp [unsignedUnits,units]

theorem unsigned_le {a b : Nat} : unsignedUnits a ≤ unsignedUnits b ↔ a ≤ b :=
  unsigned_strict.le_iff_le

theorem unsigned_pos {a : Nat} : 0 < unsignedUnits a ↔ 0 < a := by
  rw [← unsigned_zero]
  exact unsigned_strict.lt_iff_lt

def signedUnits (w : Nat) : ℚ :=
  if w < signBit then unsignedUnits (magnitude w) else -(unsignedUnits (magnitude w) : ℚ)

theorem fraction_magnitude (w : Nat) : Binary64.fraction w = magnitude w % 2^52 := by
  unfold Binary64.fraction magnitude signBit
  omega

theorem decode_signed {w : Nat} {q : ℚ} (h : Binary64.decode w = some q) :
    q * (2:ℚ)^1074 = signedUnits w := by
  rw [decode_scaled h,exponent_magnitude,fraction_magnitude]
  unfold signedUnits unsignedUnits Binary64.sign signBit
  split <;> simp_all

theorem key_signed_le (u v : Nat) : key u ≤ key v ↔ signedUnits u ≤ signedUnits v := by
  have hu : magnitude u < signBit := Nat.mod_lt _ (by norm_num [signBit])
  have hv : magnitude v < signBit := Nat.mod_lt _ (by norm_num [signBit])
  have huv : ((unsignedUnits (magnitude u):ℚ) ≤ unsignedUnits (magnitude v)) ↔
      magnitude u ≤ magnitude v := by exact_mod_cast (unsigned_le (a := magnitude u) (b := magnitude v))
  have hvu : ((unsignedUnits (magnitude v):ℚ) ≤ unsignedUnits (magnitude u)) ↔
      magnitude v ≤ magnitude u := by exact_mod_cast (unsigned_le (a := magnitude v) (b := magnitude u))
  have hpu : 0 ≤ (unsignedUnits (magnitude u):ℚ) := Nat.cast_nonneg _
  have hpv : 0 ≤ (unsignedUnits (magnitude v):ℚ) := Nat.cast_nonneg _
  by_cases su : u < signBit <;> by_cases sv : v < signBit
  · simpa [key,signedUnits,su,sv] using huv.symm
  · simp only [key,signedUnits,if_pos su,if_neg sv]
    by_cases zu : magnitude u = 0 <;> by_cases zv : magnitude v = 0
    · simp [zu,zv,unsigned_zero]
    · have hp : (0:ℚ) < unsignedUnits (magnitude v) := by
        exact_mod_cast (unsigned_pos.mpr (by omega : 0 < magnitude v))
      simp only [zu,unsigned_zero,Nat.cast_zero,zero_add]
      constructor <;> intro h <;> (first | omega | linarith)
    · have hp : (0:ℚ) < unsignedUnits (magnitude u) := by
        exact_mod_cast (unsigned_pos.mpr (by omega : 0 < magnitude u))
      simp only [zv,unsigned_zero,Nat.cast_zero,neg_zero,Nat.sub_zero]
      constructor <;> intro h <;> (first | omega | linarith)
    · have hp : (0:ℚ) < unsignedUnits (magnitude u) := by
        exact_mod_cast (unsigned_pos.mpr (by omega : 0 < magnitude u))
      constructor <;> intro h <;> (first | omega | linarith)
  · simp only [key,signedUnits,if_neg su,if_pos sv]
    constructor
    · intro _; linarith
    · intro _; omega
  · simp only [key,signedUnits,if_neg su,if_neg sv,neg_le_neg_iff]
    rw [hvu]
    omega

theorem decoded_key_le {u v : Nat} {a b : ℚ}
    (hu : Binary64.decode u = some a) (hv : Binary64.decode v = some b) :
    key u ≤ key v ↔ a ≤ b := by
  rw [key_signed_le,← decode_signed hu,← decode_signed hv]
  exact mul_le_mul_right (by positivity : (0:ℚ) < 2^1074)

theorem decoded_key_lt {u v : Nat} {a b : ℚ}
    (hu : Binary64.decode u = some a) (hv : Binary64.decode v = some b) :
    key u < key v ↔ a < b := by
  simp only [← not_le]
  exact not_congr (decoded_key_le hv hu)

theorem decoded_key_eq {u v : Nat} {a b : ℚ}
    (hu : Binary64.decode u = some a) (hv : Binary64.decode v = some b) :
    key u = key v ↔ a = b := by
  rw [le_antisymm_iff,decoded_key_le hu hv,decoded_key_le hv hu,le_antisymm_iff]

end GeneralizedIntervalArithmetic.Binary64Key
