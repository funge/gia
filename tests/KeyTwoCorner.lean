import KeyTwoCorner
import AuditPolicy
namespace GeneralizedIntervalArithmetic.KeyTwoCornerChecks
open Binary64Key

-- Reference-dispatch regressions for the later exact request-equivalence theorem.
-- These use raw Nat words throughout; no native Float/DAZ comparison occurs.
set_option exponentiation.threshold 2048
macro "reference_check" : tactic => `(tactic| decide)

theorem zero_lower_request : KeyTwoCorner.requests
    ⟨0x8000000000000000,0x3ff0000000000000⟩
    ⟨0x4000000000000000,0x4010000000000000⟩ =
    some ((0x8000000000000000,0x4010000000000000),
      (0x3ff0000000000000,0x4000000000000000)) := by reference_check

theorem negative_zero_priority : KeyTwoCorner.requests
    ⟨0x8000000000000000,0x8000000000000000⟩
    ⟨0x4000000000000000,0x4010000000000000⟩ =
    some ((0x8000000000000000,0x4010000000000000),
      (0x8000000000000000,0x4000000000000000)) := by reference_check

theorem reversed_zero_bits : KeyTwoCorner.requests
    ⟨0,0x8000000000000000⟩ ⟨0x4000000000000000,0x4010000000000000⟩ =
    some ((0,0x4010000000000000),(0x8000000000000000,0x4000000000000000)) := by
  reference_check

theorem oversized_numerator_no_calls (call) : KeyTwoCorner.run call
    ⟨2^64,0x3ff0000000000000⟩ ⟨0x4000000000000000,0x4010000000000000⟩ =
    ([],none) := by
  apply KeyTwoCorner.rejected_no_calls
  reference_check

theorem oversized_valid_word_no_calls (call) : KeyTwoCorner.run call
    ⟨2^64+0x3ff0000000000000,0x3ff0000000000000⟩
    ⟨0x4000000000000000,0x4010000000000000⟩ = ([],none) := by
  apply KeyTwoCorner.rejected_no_calls
  reference_check

theorem reversed_subnormal_no_calls (call) : KeyTwoCorner.run call
    ⟨2,1⟩ ⟨0x4000000000000000,0x4010000000000000⟩ = ([],none) := by
  apply KeyTwoCorner.rejected_no_calls
  reference_check

theorem oversized_key_no_wrap : checkedKey (2^64+0x3ff0000000000000) = none := by decide

theorem six_rows :
    KeyTwoCorner.requests ⟨0x3ff0000000000000,0x4000000000000000⟩ ⟨0x4000000000000000,0x4010000000000000⟩ = some ((0x3ff0000000000000,0x4010000000000000),(0x4000000000000000,0x4000000000000000)) ∧
    KeyTwoCorner.requests ⟨0xc000000000000000,0xbff0000000000000⟩ ⟨0x4000000000000000,0x4010000000000000⟩ = some ((0xc000000000000000,0x4000000000000000),(0xbff0000000000000,0x4010000000000000)) ∧
    KeyTwoCorner.requests ⟨0xc000000000000000,0x4000000000000000⟩ ⟨0x4000000000000000,0x4010000000000000⟩ = some ((0xc000000000000000,0x4000000000000000),(0x4000000000000000,0x4000000000000000)) ∧
    KeyTwoCorner.requests ⟨0x3ff0000000000000,0x4000000000000000⟩ ⟨0xc010000000000000,0xc000000000000000⟩ = some ((0x4000000000000000,0xc000000000000000),(0x3ff0000000000000,0xc010000000000000)) ∧
    KeyTwoCorner.requests ⟨0xc000000000000000,0xbff0000000000000⟩ ⟨0xc010000000000000,0xc000000000000000⟩ = some ((0xbff0000000000000,0xc010000000000000),(0xc000000000000000,0xc000000000000000)) ∧
    KeyTwoCorner.requests ⟨0xc000000000000000,0x4000000000000000⟩ ⟨0xc010000000000000,0xc000000000000000⟩ = some ((0x4000000000000000,0xc000000000000000),(0xc000000000000000,0xc000000000000000)) := by decide

theorem unavailable_first (call : Nat → Nat → Option (Nat × Nat))
    (h : call 0x3ff0000000000000 0x4000000000000000 = none) :
    KeyTwoCorner.run call ⟨0x3ff0000000000000,0x4000000000000000⟩
      ⟨0x3ff0000000000000,0x4000000000000000⟩ =
      ([(0x3ff0000000000000,0x4000000000000000)],none) := by
  have hp : KeyTwoCorner.requests ⟨0x3ff0000000000000,0x4000000000000000⟩
      ⟨0x3ff0000000000000,0x4000000000000000⟩ =
      some ((0x3ff0000000000000,0x4000000000000000),(0x4000000000000000,0x3ff0000000000000)) := by decide
  simp [KeyTwoCorner.run,hp,h]

end GeneralizedIntervalArithmetic.KeyTwoCornerChecks
#audit_namespace GeneralizedIntervalArithmetic.KeyTwoCornerChecks
