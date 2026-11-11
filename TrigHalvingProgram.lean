import SineProgram
import QuadrantProgram

namespace GeneralizedIntervalArithmetic.HardwareHalving
open HardwareAddition

/-- Reduce the local argument, then reconstruct both functions. No error-free
transform or exact-halving assumption is used. -/
def run {F : Type} {m : Type → Type} [Monad m]
    (mul sub div : Bounds F → Bounds F → m (Option (Bounds F)))
    (sin cos : Bounds F → m (Option (Bounds F))) (two one : Bounds F) :
    Nat → Bounds F → m (Option (Bounds F × Bounds F))
  | 0, I => do
    let some S ← sin I | return none
    let some C ← cos I | return none
    return some (S,C)
  | n+1, I => do
    let some H ← div I two | return none
    let some (S,C) ← run mul sub div sin cos two one n H | return none
    let some TS ← mul two S | return none
    let some S2 ← mul TS C | return none
    let some CC ← mul C C | return none
    let some TCC ← mul two CC | return none
    let some C2 ← sub TCC one | return none
    return some (S2,C2)

def sine {F : Type} {m : Type → Type} [Monad m]
    (mul sub div : Bounds F → Bounds F → m (Option (Bounds F)))
    (sin cos : Bounds F → m (Option (Bounds F))) (two one : Bounds F)
    (depth : Nat) (I : Bounds F) : m (Option (Bounds F)) := do
  let some (S,_) ← run mul sub div sin cos two one depth I | return none
  return some S

def cosine {F : Type} {m : Type → Type} [Monad m]
    (mul sub div : Bounds F → Bounds F → m (Option (Bounds F)))
    (sin cos : Bounds F → m (Option (Bounds F))) (two one : Bounds F)
    (depth : Nat) (I : Bounds F) : m (Option (Bounds F)) := do
  let some (_,C) ← run mul sub div sin cos two one depth I | return none
  return some C

/-- Keep the established enclosure if refinement fails; otherwise intersect
both sound answers. This prevents wider intervals from regressing. -/
def refine {F : Type} {m : Type → Type} [Monad m]
    (old new : Bounds F → m (Option (Bounds F)))
    (lt : F → F → Bool) (mn mx : F → F → F) (I : Bounds F) : m (Option (Bounds F)) := do
  let some A ← old I | return none
  match ← new I with
  | none => return some A
  | some B => return HardwareQuadrants.clip lt mn mx A B

end GeneralizedIntervalArithmetic.HardwareHalving
