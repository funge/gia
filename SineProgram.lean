import HardwareBounds

namespace GeneralizedIntervalArithmetic.HardwareSine
open HardwareAddition

/-- The finite interpretation and comparison contract justify this restricted guard.
Exceptional values are additionally rejected by the native wrapper. -/
def unitGuard {F : Type} (lt : F → F → Bool) (zero one : F) (I : Bounds F) : Bool :=
  !lt I.lo zero && !lt one I.hi && !lt I.hi I.lo

/-- Shared straight-line program. IO uses existing directed interval operations;
the logical specialization uses observed successful results through a pure oracle.
No system sine or rational arithmetic is called by the native specialization. -/
def run {F : Type} {m : Type → Type} [Monad m]
    (supported : Bounds F → Bool)
    (add sub mul div : Bounds F → Bounds F → m (Option (Bounds F)))
    (zero : F) (six oneTwenty fiveThousandForty : Bounds F)
    (input : Bounds F) : m (Option (Bounds F)) := do
  if !supported input then return none
  let some x2 ← mul input input | return none
  let some x3 ← mul x2 input | return none
  let some x5 ← mul x3 x2 | return none
  let some x7 ← mul x5 x2 | return none
  let some third ← div x3 six | return none
  let some fifth ← div x5 oneTwenty | return none
  let some error ← div x7 fiveThousandForty | return none
  let some difference ← sub input third | return none
  let some polynomial ← add difference fifth | return none
  sub polynomial ⟨zero, error.hi⟩

end GeneralizedIntervalArithmetic.HardwareSine
