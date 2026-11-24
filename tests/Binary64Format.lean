import Binary64Format
import AuditPolicy

namespace GeneralizedIntervalArithmetic.Binary64FormatChecks
open Binary64Format FormatDigits
set_option exponentiation.threshold 2048

macro "decode_raw" : tactic => `(tactic| norm_num [Binary64.decode,Binary64.exponent,Binary64.fraction,Binary64.sign])

theorem zero_signs : Binary64.decode 0 = some 0 ∧
    Binary64.decode 0x8000000000000000 = some 0 ∧
    Repaired format 0 ∧ (0:Binary64.Word) ≠ 0x8000000000000000 := by
  have h : Binary64.decode 0 = some 0 := by decode_raw
  exact ⟨h,by decode_raw,decoded_repaired h,by decide⟩

theorem smallest_subnormal : Binary64.decode 1 = some (1/(2:ℚ)^1074) ∧
    Repaired format (1/(2:ℚ)^1074) := by
  have h : Binary64.decode 1 = some (1/(2:ℚ)^1074) := by decode_raw
  exact ⟨h,decoded_repaired h⟩

theorem negative_subnormal : Repaired format (-1/(2:ℚ)^1074) := by
  apply decoded_repaired (w:=0x8000000000000001)
  decode_raw

theorem normal_transition :
    Repaired format (((2:ℚ)^52-1)/2^1074) ∧ Repaired format (1/(2:ℚ)^1022) := by
  constructor
  · apply decoded_repaired (w:=0x000fffffffffffff); decode_raw
  · apply decoded_repaired (w:=0x0010000000000000); decode_raw

theorem extreme_finite : Repaired format (((2:ℚ)^53-1)*2^971) ∧
    Repaired format (-(((2:ℚ)^53-1)*2^971)) := by
  constructor
  · apply decoded_repaired (w:=0x7fefffffffffffff); decode_raw
  · apply decoded_repaired (w:=0xffefffffffffffff); decode_raw

/-- The converse covers leading zeros well above the minimum, not only canonical inputs. -/
theorem unnormalized_converse : ∃ w, Binary64.decode w = some (eval format 1 0) := by
  apply (repaired_iff_decode _).mp
  exact ⟨1,0,by norm_num [Admitted,format],by norm_num [format],by norm_num [format],Or.inl rfl⟩

theorem minimum_and_normal_pack :
    pack false 0 1 = 1 ∧ pack false 1 0 = 0x0010000000000000 ∧
    pack true 2046 (2^52-1) = 0xffefffffffffffff := by norm_num [pack]

theorem source_minimum_branch : NormalOrMinimum format (significand 1) (exponent 1) ∧
    ¬ Normalized format (significand 1) := by
  have h : Binary64.decode 1 = some (1/(2:ℚ)^1074) := by decode_raw
  exact ⟨decode_presentation h,by norm_num [Normalized,significand,Binary64.exponent,Binary64.fraction,format]⟩

theorem nonfinite_and_oversized : Binary64.decode 0x7ff0000000000000 = none ∧
    Binary64.decode 0x7ff8000000000000 = none ∧
    Binary64.decode 0x7ff0000000000001 = none ∧ Binary64.decode (2^64+1) = none := by decode_raw

/-- A proof-side mathematical demotion client, not a native rounding test. -/
theorem finite_demotion_client :
    DiscreteDemotion.down DiscreteDemotion.binaryValues (0:EReal) = 0 ∧
    DiscreteDemotion.up DiscreteDemotion.binaryValues (0:EReal) = 0 := by
  simpa using repaired_fixed zero_signs.2.2.1

end GeneralizedIntervalArithmetic.Binary64FormatChecks
#audit_namespace GeneralizedIntervalArithmetic.Binary64FormatChecks
