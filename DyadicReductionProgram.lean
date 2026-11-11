import SineReductionProgram

namespace GeneralizedIntervalArithmetic.HardwareSine
open HardwareAddition

/-- Generate coefficients by directed doubling. Their integer witnesses are
proved separately; the runtime performs no Float-to-integer conversion. -/
def doubledPeriods {F : Type} {m : Type → Type} [Monad m]
    (add : Bounds F → Bounds F → m (Option (Bounds F))) :
    Nat → Bounds F → m (Option (List (Bounds F)))
  | 0, _ => pure (some [])
  | n+1, C => do
    let some D ← add C C | return none
    let some rest ← doubledPeriods add n D | return none
    return some (C :: rest)

/-- Each accepted shift is a certified whole period. Selection affects precision,
not soundness. Failure remains explicit; a separate global bound may handle it. -/
def sweepPeriods {F : Type} {m : Type → Type} [Monad m]
    (mul sub : Bounds F → Bounds F → m (Option (Bounds F)))
    (accept : Bounds F → Bounds F → Bool)
    (kernel : Bounds F → m (Option (Bounds F))) (P : Bounds F) :
    List (Bounds F) → Bounds F → m (Option (Bounds F))
  | [], I => kernel I
  | C :: cs, I => do
    let some shift ← mul C P | return none
    if accept I shift then
      let some R ← sub I shift | return none
      sweepPeriods mul sub accept kernel P cs R
    else sweepPeriods mul sub accept kernel P cs I

def dyadicRun {F : Type} {m : Type → Type} [Monad m]
    (add mul sub : Bounds F → Bounds F → m (Option (Bounds F)))
    (accept : Bounds F → Bounds F → Bool)
    (kernel : Bounds F → m (Option (Bounds F)))
    (P positive negative : Bounds F) (fuel : Nat) (I : Bounds F) :
    m (Option (Bounds F)) := do
  let some ps ← doubledPeriods add fuel positive | return none
  let some ns ← doubledPeriods add fuel negative | return none
  sweepPeriods mul sub accept kernel P (ps.reverse ++ ns.reverse) I

end GeneralizedIntervalArithmetic.HardwareSine
