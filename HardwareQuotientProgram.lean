import HardwareEvaluatorProgram

namespace GeneralizedIntervalArithmetic.HardwareQuotient
open HardwareAddition HardwareEvaluator

inductive Operation where
  | add | sub | mul | div
  deriving Repr, DecidableEq, Inhabited

/-- Reuse existing polynomial leaves; this layer composes them and quotients.
No quotient is represented as an affine function. -/
inductive Expression (C : Type) where
  | polynomial : Polynomial C → Expression C
  | binary : Operation → Expression C → Expression C → Expression C
  deriving Repr, Inhabited

structure Tracks (F : Type) where
  ordinary : Option (Bounds F)
  refined : Result F
  deriving Repr

def polynomialTracks {F : Type} (lt : F → F → Bool) (mn mx : F → F → F)
    (ordinary : Option (Bounds F)) (affine : Option (HardwareAffine.Form F)) : Tracks F :=
  ⟨ordinary,merge lt mn mx ordinary (affine.map (HardwareAffine.hull mn mx))⟩

def attempt {F : Type} {m : Type → Type} [Monad m]
    (op : Bounds F → Bounds F → m (Option (Bounds F)))
    (I J : Option (Bounds F)) : m (Option (Bounds F)) := do
  let some a := I | return none
  let some b := J | return none
  op a b

def available {F : Type} : Result F → Option (Bounds F)
  | .bound I => some I
  | _ => none

def step {F : Type} {m : Type → Type} [Monad m]
    (op : Bounds F → Bounds F → m (Option (Bounds F)))
    (lt : F → F → Bool) (mn mx : F → F → F) (I J : Tracks F) : m (Tracks F) := do
  let O ← attempt op I.ordinary J.ordinary
  match I.refined, J.refined with
  | .conflict, _ | _, .conflict => return ⟨O,.conflict⟩
  | _, _ =>
    let R ← attempt op (available I.refined) (available J.refined)
    return ⟨O,merge lt mn mx O R⟩

@[nospecialize]
def eval {C F : Type} {m : Type → Type} [Monad m]
    (leaf : Polynomial C → m (Tracks F))
    (op : Operation → Bounds F → Bounds F → m (Option (Bounds F)))
    (lt : F → F → Bool) (mn mx : F → F → F) : Expression C → m (Tracks F)
  | .polynomial p => leaf p
  | .binary k a b => do
    let A ← eval leaf op lt mn mx a
    let B ← eval leaf op lt mn mx b
    step (op k) lt mn mx A B

end GeneralizedIntervalArithmetic.HardwareQuotient
