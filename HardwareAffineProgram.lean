import HardwareBounds

namespace GeneralizedIntervalArithmetic.HardwareAffine
open HardwareAddition

/-- Finite affine enclosure represented by intervals at the two parameter endpoints.
Validity is explicit; the runtime carries no proof or rational coefficients. -/
structure Form (F : Type) where
  atZero : Bounds F
  atOne : Bounds F
  deriving Repr

/-- Shared implementation of affine addition and subtraction. -/
def combine {F : Type} {m : Type → Type} [Monad m]
    (op : Bounds F → Bounds F → m (Option (Bounds F)))
    (I J : Form F) : m (Option (Form F)) := do
  let some A ← op I.atZero J.atZero | return none
  let some B ← op I.atOne J.atOne | return none
  return some ⟨A,B⟩

/-- The same scalar interval is used at both endpoints. Soundness uses one
common real scalar witness, including for negative scalars. -/
def scale {F : Type} {m : Type → Type} [Monad m]
    (mul : Bounds F → Bounds F → m (Option (Bounds F)))
    (scalar : Bounds F) (I : Form F) : m (Option (Form F)) := do
  let some A ← mul scalar I.atZero | return none
  let some B ← mul scalar I.atOne | return none
  return some ⟨A,B⟩

/-- Conservative demotion that forgets the shared parameter. -/
def hull {F : Type} (mn mx : F → F → F) (I : Form F) : Bounds F :=
  ⟨mn I.atZero.lo I.atOne.lo, mx I.atZero.hi I.atOne.hi⟩

end GeneralizedIntervalArithmetic.HardwareAffine
