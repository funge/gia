import Binary64Key
import AuditPolicy
namespace GeneralizedIntervalArithmetic.Binary64KeyChecks
open Binary64Key

theorem finite_edges :
    finite 0 = true ∧ finite 0x8000000000000000 = true ∧
    finite 1 = true ∧ finite 0x000fffffffffffff = true ∧
    finite 0x0010000000000000 = true ∧ finite 0x7fefffffffffffff = true ∧
    finite 0xffefffffffffffff = true := by decide

theorem rejected_edges :
    checkedKey 0x7ff0000000000000 = none ∧
    checkedKey 0xfff0000000000000 = none ∧
    checkedKey 0x7ff8000000000001 = none ∧
    checkedKey 0x7ff0000000000001 = none ∧
    checkedKey (2^64) = none ∧ checkedKey (2^64+1) = none := by decide

theorem signed_zero_tie :
    key64 0 = key64 0x8000000000000000 ∧
    key64 0 = 0x8000000000000000 := by decide

theorem normal_transition :
    key64 0x000fffffffffffff < key64 0x0010000000000000 ∧
    key64 0x8010000000000000 < key64 0x800fffffffffffff := by decide

theorem adjacent_binade :
    key64 0x3fffffffffffffff < key64 0x4000000000000000 ∧
    key64 0xc000000000000000 < key64 0xbfffffffffffffff := by decide

theorem extremes :
    key64 0xffefffffffffffff < key64 0x8000000000000001 ∧
    key64 0x8000000000000001 < key64 0 ∧
    key64 0 < key64 1 ∧ key64 1 < key64 0x7fefffffffffffff := by decide

theorem units_normal_transition :
    units 0 (2^52-1) = 2^52-1 ∧ units 1 0 = 2^52 := by decide

theorem units_next_binade :
    units 1 (2^52-1) < units 2 0 := by decide

theorem concrete_uint_bridge :
    (checkedKey 0xbff0000000000000).map UInt64.toNat =
      some (key 0xbff0000000000000) := by
  rw [checkedKey_spec]
  rfl

-- Reference-dispatch regressions for the later exact request-equivalence theorem.
-- These use raw Nat words throughout; no native Float/DAZ comparison occurs.
set_option exponentiation.threshold 2048
macro "reference_check" : tactic => `(tactic| norm_num [WordTwoCorner.requests,
  WordTwoCorner.validate,WordTwoCorner.pick,Binary64.decode,Binary64.exponent,
  Binary64.fraction,Binary64.sign])

theorem zero_lower_request : WordTwoCorner.requests
    ⟨0x8000000000000000,0x3ff0000000000000⟩
    ⟨0x4000000000000000,0x4010000000000000⟩ =
    some ((0x8000000000000000,0x4010000000000000),
      (0x3ff0000000000000,0x4000000000000000)) := by reference_check

theorem negative_zero_priority : WordTwoCorner.requests
    ⟨0x8000000000000000,0x8000000000000000⟩
    ⟨0x4000000000000000,0x4010000000000000⟩ =
    some ((0x8000000000000000,0x4010000000000000),
      (0x8000000000000000,0x4000000000000000)) := by reference_check

theorem reversed_zero_bits : WordTwoCorner.requests
    ⟨0,0x8000000000000000⟩ ⟨0x4000000000000000,0x4010000000000000⟩ =
    some ((0,0x4010000000000000),(0x8000000000000000,0x4000000000000000)) := by
  reference_check

theorem oversized_numerator_no_calls (call) : WordTwoCorner.run call
    ⟨2^64,0x3ff0000000000000⟩ ⟨0x4000000000000000,0x4010000000000000⟩ =
    ([],none) := by
  apply WordTwoCorner.rejected_no_calls
  reference_check

theorem oversized_valid_word_no_calls (call) : WordTwoCorner.run call
    ⟨2^64+0x3ff0000000000000,0x3ff0000000000000⟩
    ⟨0x4000000000000000,0x4010000000000000⟩ = ([],none) := by
  apply WordTwoCorner.rejected_no_calls
  reference_check

theorem reversed_subnormal_no_calls (call) : WordTwoCorner.run call
    ⟨2,1⟩ ⟨0x4000000000000000,0x4010000000000000⟩ = ([],none) := by
  apply WordTwoCorner.rejected_no_calls
  reference_check

theorem oversized_key_no_wrap : checkedKey (2^64+0x3ff0000000000000) = none := by decide

end GeneralizedIntervalArithmetic.Binary64KeyChecks
#audit_namespace GeneralizedIntervalArithmetic.Binary64KeyChecks
