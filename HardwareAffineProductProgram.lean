import HardwareAffineProgram

namespace GeneralizedIntervalArithmetic.HardwareAffine
open HardwareAddition

/-- Endpoint chord minus a uniformly enclosed quadratic residual. The result is
another affine form. Every failed intermediate returns unknown. -/
def product {F : Type} {m : Type → Type} [Monad m]
    (sub mul : Bounds F → Bounds F → m (Option (Bounds F)))
    (bubble : Bounds F) (I J : Form F) : m (Option (Form F)) := do
  let some P ← combine mul I J | return none
  let some D ← sub I.atOne I.atZero | return none
  let some E ← sub J.atOne J.atZero | return none
  let some C ← mul D E | return none
  let some R ← mul C bubble | return none
  combine sub P ⟨R,R⟩

end GeneralizedIntervalArithmetic.HardwareAffine
