import Binary64
import AuditPolicy

namespace GeneralizedIntervalArithmetic.Binary64Checks
open Binary64
set_option exponentiation.threshold 2048

macro "decode_word" : tactic => `(tactic| norm_num [decode,exponent,fraction,sign])

theorem invalid_word : decode (2^64) = none ∧ decode (2^64+1) = none := by decode_word

theorem signed_zero : decode 0 = some 0 ∧ decode 0x8000000000000000 = some 0 := by decode_word

theorem min_subnormal : decode 1 = some (1/(2:ℚ)^1074) ∧
    decode 0x8000000000000001 = some (-1/(2:ℚ)^1074) := by decode_word

theorem max_subnormal : decode 0x000fffffffffffff = some (((2:ℚ)^52-1)/2^1074) := by decode_word

theorem min_normal : decode 0x0010000000000000 = some (1/(2:ℚ)^1022) := by decode_word

theorem transition_gap : (1/(2:ℚ)^1022)-((2:ℚ)^52-1)/2^1074 = 1/(2:ℚ)^1074 := by norm_num

theorem unit : decode 0x3ff0000000000000 = some 1 ∧
    decode 0xbff0000000000000 = some (-1) := by decode_word

theorem scale_boundary : decode 0x4330000000000000 = some ((2:ℚ)^52) ∧
    decode 0x4340000000000000 = some ((2:ℚ)^53) := by decode_word

theorem max_finite : decode 0x7fefffffffffffff = some (((2:ℚ)^53-1)*2^971) ∧
    decode 0xffefffffffffffff = some (-(((2:ℚ)^53-1)*2^971)) := by decode_word

theorem infinities : decode 0x7ff0000000000000 = none ∧
    decode 0xfff0000000000000 = none := by decode_word

theorem nan_payloads : decode 0x7ff0000000000001 = none ∧
    decode 0xfff0000000000001 = none ∧ decode 0x7ff8000000000000 = none ∧
    decode 0xffffffffffffffff = none := by decode_word

-- Direct client of the existing enclosure predicates, with no decoder premises.
theorem constants_enclose :
    HardwareAddition.Contains real (⟨0x400921fb54442d18,0x400921fb54442d19⟩ : HardwareAddition.Bounds Word) Real.pi ∧
    HardwareAddition.Contains real (⟨0x3ca1a60d3bc55bea,0x3ca1a66bae498e34⟩ : HardwareAddition.Bounds Word)
      (Real.pi-HardwarePi.lower) := ⟨pi_contains,tail_contains⟩

#audit_namespace GeneralizedIntervalArithmetic.Binary64Checks
end GeneralizedIntervalArithmetic.Binary64Checks
