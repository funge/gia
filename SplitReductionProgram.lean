import DyadicReductionProgram

namespace GeneralizedIntervalArithmetic.HardwareSine
open HardwareAddition

/-- Keep the small correction separate until coarse cancellation finishes. -/
def sweepSplit {F : Type} {m : Type → Type} [Monad m]
    (add mul sub : Bounds F → Bounds F → m (Option (Bounds F)))
    (accept : Bounds F → Bounds F → Bool)
    (kernel : Bounds F → m (Option (Bounds F))) (H T : Bounds F) :
    List (Bounds F) → Bounds F → Bounds F → m (Option (Bounds F))
  | [], I, L => do
    let some R ← sub I L | return none
    kernel R
  | C :: cs, I, L => do
    let some shift ← mul C H | return none
    if accept I shift then
      let some R ← sub I shift | return none
      let some correction ← mul C T | return none
      let some A ← add L correction | return none
      sweepSplit add mul sub accept kernel H T cs R A
    else sweepSplit add mul sub accept kernel H T cs I L

def splitRun {F : Type} {m : Type → Type} [Monad m]
    (add mul sub : Bounds F → Bounds F → m (Option (Bounds F)))
    (accept : Bounds F → Bounds F → Bool)
    (kernel : Bounds F → m (Option (Bounds F)))
    (H T positive negative : Bounds F) (zero : F) (fuel : Nat) (I : Bounds F) :
    m (Option (Bounds F)) := do
  let some ps ← doubledPeriods add fuel positive | return none
  let some ns ← doubledPeriods add fuel negative | return none
  sweepSplit add mul sub accept kernel H T (ps.reverse ++ ns.reverse) I ⟨zero,zero⟩

end GeneralizedIntervalArithmetic.HardwareSine
