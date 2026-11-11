import SineProgram

namespace GeneralizedIntervalArithmetic.HardwareCosine
open HardwareAddition

/-- Natural interval evaluation handles intervals crossing zero without an invalid
monotone-endpoint rule. The final cap uses cos x ≤ 1. -/
def run {F : Type} {m : Type → Type} [Monad m]
    (supported : Bounds F → Bool)
    (add sub mul div : Bounds F → Bounds F → m (Option (Bounds F)))
    (mn : F → F → F) (zero one : F) (two c24 c720 c40320 : Bounds F)
    (input : Bounds F) : m (Option (Bounds F)) := do
  if !supported input then return none
  let some x2 ← mul input input | return none
  let some x4 ← mul x2 x2 | return none
  let some x6 ← mul x4 x2 | return none
  let some x8 ← mul x4 x4 | return none
  let some second ← div x2 two | return none
  let some fourth ← div x4 c24 | return none
  let some sixth ← div x6 c720 | return none
  let some error ← div x8 c40320 | return none
  let some a ← sub ⟨one, one⟩ second | return none
  let some b ← add a fourth | return none
  let some p ← sub b sixth | return none
  let some result ← add p ⟨zero, error.hi⟩ | return none
  return some ⟨result.lo, mn result.hi one⟩

end GeneralizedIntervalArithmetic.HardwareCosine
