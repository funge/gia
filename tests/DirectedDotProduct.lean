import DirectedDotProduct
import AuditPolicy
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace GeneralizedIntervalArithmetic.DirectedDotProductChecks
open DirectedDotProduct HardwareAddition

def decode (q : ℚ) : Option ℝ := some (q:ℝ)
def exactAdd (a b : ℚ) : Option (ℚ × ℚ) := some (a+b,a+b)
def exactMul (a b : ℚ) : Option (ℚ × ℚ) := some (a*b,a*b)
def looseAdd (a b : ℚ) : Option (ℚ × ℚ) := some (a+b-1,a+b+1)
def looseMul (a b : ℚ) : Option (ℚ × ℚ) := some (a*b-1,a*b+1)

theorem exact_add_sound (a b : ℚ) : HardwareAddition.CallSound decode a b (exactAdd a b) := by
  simp [HardwareAddition.CallSound,decode,exactAdd]
theorem exact_mul_sound (a b : ℚ) : HardwareMultiplication.CallSound decode a b (exactMul a b) := by
  simp [HardwareMultiplication.CallSound,decode,exactMul]
theorem min_sound : HardwareMultiplication.SelectSound decode min min := by
  simp [HardwareMultiplication.SelectSound,decode]
theorem max_sound : HardwareMultiplication.SelectSound decode max max := by
  simp [HardwareMultiplication.SelectSound,decode]

/-- Deliberately loose, but conformant, primitive observations. Not a binary64 model. -/
theorem loose_add_sound (a b : ℚ) : HardwareAddition.CallSound decode a b (looseAdd a b) := by
  simp [HardwareAddition.CallSound,decode,looseAdd]
theorem loose_mul_sound (a b : ℚ) : HardwareMultiplication.CallSound decode a b (looseMul a b) := by
  simp [HardwareMultiplication.CallSound,decode,looseMul]

def weights : Fin 2 → Bounds ℚ := ![⟨2,2⟩,⟨-1,-1⟩]
def features : Fin 2 → Bounds ℚ := ![⟨3,3⟩,⟨4,4⟩]

theorem exact_api : primitiveRun exactAdd exactMul min max 0 weights features = some ⟨2,2⟩ := by
  norm_num [primitiveRun,run,loop,weights,features,exactAdd,exactMul,assemble,
    HardwareMultiplication.assembleFour]

theorem exact_api_encloses : Contains decode (⟨2,2⟩ : Bounds ℚ)
    (IntervalDotProduct.dot (![2,-1] : Fin 2 → ℝ) ![3,4]) := by
  apply primitiveRun_encloses exact_add_sound exact_mul_sound min_sound max_sound
    (show decode 0 = some 0 by simp [decode]) _ _ exact_api
  · intro i; fin_cases i <;> norm_num [weights,Contains,decode]
  · intro i; fin_cases i <;> norm_num [features,Contains,decode]

/-- Uncertainty accumulates despite degenerate inputs: the exact answer is 2. -/
theorem loose_api : primitiveRun looseAdd looseMul min max 0 weights features = some ⟨-2,6⟩ := by
  norm_num [primitiveRun,run,loop,weights,features,looseAdd,looseMul,assemble,
    HardwareMultiplication.assembleFour]

theorem loose_api_encloses : Contains decode (⟨-2,6⟩ : Bounds ℚ)
    (IntervalDotProduct.dot (![2,-1] : Fin 2 → ℝ) ![3,4]) := by
  apply primitiveRun_encloses loose_add_sound loose_mul_sound min_sound max_sound
    (show decode 0 = some 0 by simp [decode]) _ _ loose_api
  · intro i; fin_cases i <;> norm_num [weights,Contains,decode]
  · intro i; fin_cases i <;> norm_num [features,Contains,decode]

def secondFails (a b : ℚ) : Option (ℚ × ℚ) := if a = -1 then none else exactMul a b

theorem later_failure_unknown : primitiveRun exactAdd secondFails min max 0 weights features = none := by
  norm_num [primitiveRun,run,loop,weights,features,secondFails,exactAdd,exactMul,
    assemble,HardwareMultiplication.assembleFour]

theorem add_failure_unknown :
    primitiveRun (fun _ _ : ℚ => none) exactMul min max 0 weights features = none := by
  norm_num [primitiveRun,run,loop,weights,features,exactMul,assemble,HardwareMultiplication.assembleFour]

/-- Failure does not imply the real expression has no value. -/
theorem failed_but_defined :
    primitiveRun exactAdd secondFails min max 0 weights features = none ∧
    IntervalDotProduct.dot (![2,-1] : Fin 2 → ℝ) ![3,4] = 2 := by
  exact ⟨later_failure_unknown,by norm_num [IntervalDotProduct.dot,Fin.sum_univ_succ]⟩

theorem empty_no_operations (I J : Fin 0 → Bounds ℚ) :
    primitiveRun (fun _ _ => none) (fun _ _ => none) min max 0 I J = some ⟨0,0⟩ := rfl

#eval primitiveRun exactAdd exactMul min max 0 weights features
#eval primitiveRun looseAdd looseMul min max 0 weights features
#eval primitiveRun exactAdd secondFails min max 0 weights features

end GeneralizedIntervalArithmetic.DirectedDotProductChecks
#audit_namespace GeneralizedIntervalArithmetic.DirectedDotProductChecks
