import SineProgram

namespace GeneralizedIntervalArithmetic.HardwareSine
open HardwareAddition

/-- Try a whole-period shift. The coefficient encloses twice an integer;
its certificate is mathematical, not a rounded quotient guess. -/
def reduce {F : Type} {m : Type → Type} [Monad m]
    (mul sub : Bounds F → Bounds F → m (Option (Bounds F)))
    (kernel : Bounds F → m (Option (Bounds F)))
    (pi coefficient input : Bounds F) : m (Option (Bounds F)) := do
  let some shift ← mul coefficient pi | return none
  let some residual ← sub input shift | return none
  kernel residual

/-- Finite search; exhaustion means unknown, never absence or undefinedness. -/
def searchPeriods {F : Type} {m : Type → Type} [Monad m]
    (mul sub : Bounds F → Bounds F → m (Option (Bounds F)))
    (kernel : Bounds F → m (Option (Bounds F)))
    (pi input : Bounds F) : List (Bounds F) → m (Option (Bounds F))
  | [] => pure none
  | c :: cs => do
      let result ← reduce mul sub kernel pi c input
      match result with
      | some O => pure (some O)
      | none => searchPeriods mul sub kernel pi input cs

/-- Small exactly representable coefficients: periods 0, +1, -1, +2, -2. -/
def periodCandidates {F : Type} (zero two negTwo four negFour : F) : List (Bounds F) :=
  [⟨zero, zero⟩, ⟨two, two⟩, ⟨negTwo, negTwo⟩, ⟨four, four⟩, ⟨negFour, negFour⟩]

end GeneralizedIntervalArithmetic.HardwareSine
