import WordTwoCorner
import AuditPolicy

namespace GeneralizedIntervalArithmetic.WordTwoCornerChecks
open WordTwoCorner HardwareAddition
set_option exponentiation.threshold 2048

def one : Word := 0x3ff0000000000000
def two : Word := 0x4000000000000000
def three : Word := 0x4008000000000000
def half : Word := 0x3fe0000000000000
def negOne : Word := 0xbff0000000000000
def negTwo : Word := 0xc000000000000000
def negFour : Word := 0xc010000000000000
def negZero : Word := 0x8000000000000000
def negTiny : Word := 0x8000000000000001
def inf : Word := 0x7ff0000000000000
def nan : Word := 0x7ff8000000000001

macro "plan_check" : tactic => `(tactic| norm_num [requests,validate,pick,
  one,two,three,half,negOne,negTwo,negFour,negZero,negTiny,inf,nan,
  Binary64.decode,Binary64.exponent,Binary64.fraction,Binary64.sign])

theorem positive_nonnegative : requests ⟨one,two⟩ ⟨one,two⟩ = some ((one,two),(two,one)) := by plan_check
theorem positive_nonpositive : requests ⟨negTwo,negOne⟩ ⟨one,two⟩ = some ((negTwo,one),(negOne,two)) := by plan_check
theorem positive_mixed : requests ⟨negTwo,three⟩ ⟨one,two⟩ = some ((negTwo,one),(three,one)) := by plan_check
theorem negative_nonnegative : requests ⟨one,two⟩ ⟨negTwo,negOne⟩ = some ((two,negOne),(one,negTwo)) := by plan_check
theorem negative_nonpositive : requests ⟨negTwo,negOne⟩ ⟨negTwo,negOne⟩ = some ((negOne,negTwo),(negTwo,negOne)) := by plan_check
theorem negative_mixed : requests ⟨negTwo,three⟩ ⟨negTwo,negOne⟩ = some ((three,negOne),(negTwo,negOne)) := by plan_check

-- These statements quantify over ANY call, not one stub that happens to fail.
theorem unused_infinite_mixed (call) : run call ⟨negTwo,three⟩ ⟨one,inf⟩ = ([],none) := by
  apply rejected_no_calls; plan_check
theorem infinite_positive (call) : run call ⟨two,three⟩ ⟨one,inf⟩ = ([],none) := by
  apply rejected_no_calls; plan_check
theorem unused_nan_mixed (call) : run call ⟨negTwo,three⟩ ⟨one,nan⟩ = ([],none) := by
  apply rejected_no_calls; plan_check
theorem nan_positive (call) : run call ⟨two,three⟩ ⟨one,nan⟩ = ([],none) := by
  apply rejected_no_calls; plan_check
theorem invalid_numerator_lower (call) : run call ⟨inf,three⟩ ⟨one,two⟩ = ([],none) := by
  apply rejected_no_calls; plan_check
theorem invalid_numerator_upper (call) : run call ⟨one,nan⟩ ⟨one,two⟩ = ([],none) := by
  apply rejected_no_calls; plan_check
theorem invalid_denominator_lower (call) : run call ⟨one,two⟩ ⟨inf,two⟩ = ([],none) := by
  apply rejected_no_calls; plan_check
theorem reversed_numerator (call) : run call ⟨three,negTwo⟩ ⟨one,two⟩ = ([],none) := by
  apply rejected_no_calls; plan_check
theorem reversed_denominator (call) : run call ⟨one,two⟩ ⟨two,one⟩ = ([],none) := by
  apply rejected_no_calls; plan_check
theorem crossing_zero (call) : run call ⟨one,two⟩ ⟨negOne,one⟩ = ([],none) := by
  apply rejected_no_calls; plan_check
theorem touching_lower_zero (call) : run call ⟨one,two⟩ ⟨negZero,one⟩ = ([],none) := by
  apply rejected_no_calls; plan_check
theorem touching_upper_zero (call) : run call ⟨one,two⟩ ⟨negOne,0⟩ = ([],none) := by
  apply rejected_no_calls; plan_check
theorem both_signed_zeros (call) : run call ⟨one,two⟩ ⟨negZero,0⟩ = ([],none) := by
  apply rejected_no_calls; plan_check
theorem oversized_word (call) : run call ⟨one,two⟩ ⟨one,2^64⟩ = ([],none) := by
  apply rejected_no_calls; plan_check

-- Original words are retained at ties; these are not native quotient-bit tests.
theorem raw_zero_selection : requests ⟨negZero,0⟩ ⟨negTwo,negOne⟩ =
    some ((0,negOne),(negZero,negTwo)) := by plan_check
theorem raw_subnormal_selection : requests ⟨negTiny,0⟩ ⟨negFour,negTwo⟩ =
    some ((0,negFour),(negTiny,negTwo)) := by plan_check

def observed (a b : Word) : Option (Word × Word) :=
  if a = one ∧ b = two then some (half,half) else
  if a = two ∧ b = one then some (two,two) else none

theorem successful_trace : run observed ⟨one,two⟩ ⟨one,two⟩ =
    ([(one,two),(two,one)],some ⟨half,two⟩) := by
  rw [run,positive_nonnegative]
  norm_num [observed,one,two,half,assemble]

theorem old_failure (mn mx : Word → Word → Word) :
    HardwareMultiplication.assembleFour mn mx (observed one one) (observed one two)
      (observed two one) (observed two two) = none := by
  norm_num [HardwareMultiplication.assembleFour,observed,one,two,half]

theorem lower_contract : HardwareDivision.CallSound Binary64.real one two (observed one two) := by
  norm_num [HardwareDivision.CallSound,HardwareMultiplication.ResultSound,Binary64.real,observed,one,two,half,
    Binary64.decode,Binary64.exponent,Binary64.fraction,Binary64.sign]
theorem upper_contract : HardwareDivision.CallSound Binary64.real two one (observed two one) := by
  norm_num [HardwareDivision.CallSound,HardwareMultiplication.ResultSound,Binary64.real,observed,one,two,half,
    Binary64.decode,Binary64.exponent,Binary64.fraction,Binary64.sign]

theorem successful_standalone {x y : ℝ}
    (hx : Contains Binary64.real ⟨one,two⟩ x) (hy : Contains Binary64.real ⟨one,two⟩ y) :
    Contains Binary64.real ⟨half,two⟩ (x/y) ∧ y ≠ 0 := by
  apply run_sound (call := observed) (I := ⟨one,two⟩) (J := ⟨one,two⟩) _ _ hx hy
  · intro p hp; rw [positive_nonnegative] at hp; cases hp
    exact ⟨lower_contract,upper_contract⟩
  · exact congrArg Prod.snd successful_trace

theorem first_failure_trace : run (fun _ _ => none) ⟨one,two⟩ ⟨one,two⟩ =
    ([(one,two)],none) := by simp [run,positive_nonnegative]

def secondFails (a b : Word) : Option (Word × Word) :=
  if a = one ∧ b = two then some (half,half) else none

theorem second_failure_trace : run secondFails ⟨one,two⟩ ⟨one,two⟩ =
    ([(one,two),(two,one)],none) := by
  rw [run,positive_nonnegative]
  norm_num [secondFails,one,two,half,assemble]

#audit_namespace GeneralizedIntervalArithmetic.WordTwoCornerChecks
end GeneralizedIntervalArithmetic.WordTwoCornerChecks
