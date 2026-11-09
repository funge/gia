namespace GeneralizedIntervalArithmetic.HardwareAddition

/-- Runtime endpoints. Validity is a semantic property, not a hidden constructor proof. -/
structure Bounds (F : Type) where
  lo : F
  hi : F
  deriving Repr

/-- Shared pure assembly, also called by the actual IO executable. -/
def assemble {F : Type} (lower upper : Option (F × F)) : Option (Bounds F) := do
  let l ← lower
  let u ← upper
  return ⟨l.1, u.2⟩

end GeneralizedIntervalArithmetic.HardwareAddition

namespace GeneralizedIntervalArithmetic.HardwareMultiplication
open HardwareAddition

/-- Runtime four-corner assembly; any unavailable corner keeps the result unknown.
The selectors are parameters, with semantic contracts in HardwareMultiplication. -/
def assembleFour {F : Type} (chooseMin chooseMax : F → F → F)
    (ll lh hl hh : Option (F × F)) : Option (Bounds F) := do
  let p₁ ← ll
  let p₂ ← lh
  let p₃ ← hl
  let p₄ ← hh
  return ⟨chooseMin (chooseMin p₁.1 p₂.1) (chooseMin p₃.1 p₄.1),
    chooseMax (chooseMax p₁.2 p₂.2) (chooseMax p₃.2 p₄.2)⟩

end GeneralizedIntervalArithmetic.HardwareMultiplication

namespace GeneralizedIntervalArithmetic.HardwareDivision
open HardwareAddition HardwareMultiplication

def awayZero {F : Type} (lt : F → F → Bool) (zero : F) (J : Bounds F) : Bool :=
  lt J.hi zero || lt zero J.lo

def assembleGuarded {F : Type} (lt : F → F → Bool) (zero : F)
    (chooseMin chooseMax : F → F → F) (J : Bounds F)
    (ll lh hl hh : Option (F × F)) : Option (Bounds F) :=
  if awayZero lt zero J then assembleFour chooseMin chooseMax ll lh hl hh else none

end GeneralizedIntervalArithmetic.HardwareDivision
