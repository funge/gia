import HardwareAffineProductProgram
import QuadrantProgram

namespace GeneralizedIntervalArithmetic.HardwareEvaluator
open HardwareAddition

/-- Finite polynomial syntax with backend constants and one shared variable. -/
inductive Polynomial (C : Type) where
  | const : C → Polynomial C
  | var : Polynomial C
  | add : Polynomial C → Polynomial C → Polynomial C
  | sub : Polynomial C → Polynomial C → Polynomial C
  | mul : Polynomial C → Polynomial C → Polynomial C
  deriving Repr, Inhabited

/-- One traversal reused by both representations; failure is local to a track. -/
-- Avoid compiler-generated opaque specialization declarations in the audited namespace.
@[nospecialize]
def eval {C A : Type} {m : Type → Type} [Monad m]
    (constant : C → m (Option A)) (input : Option A)
    (add sub mul : A → A → m (Option A)) : Polynomial C → m (Option A)
  | .const c => constant c
  | .var => pure input
  | .add a b => do
      let some x ← eval constant input add sub mul a | return none
      let some y ← eval constant input add sub mul b | return none
      add x y
  | .sub a b => do
      let some x ← eval constant input add sub mul a | return none
      let some y ← eval constant input add sub mul b | return none
      sub x y
  | .mul a b => do
      let some x ← eval constant input add sub mul a | return none
      let some y ← eval constant input add sub mul b | return none
      mul x y

/-- Exact endpoint parameterization of an ordinary input interval. -/
def seed {F : Type} (I : Bounds F) : HardwareAffine.Form F :=
  ⟨⟨I.lo,I.lo⟩,⟨I.hi,I.hi⟩⟩

/-- Reuse the traversal with the existing affine operators. -/
def affineEval {C F : Type} {m : Type → Type} [Monad m]
    (constant : C → m (Option (HardwareAffine.Form F)))
    (input : Option (HardwareAffine.Form F))
    (add sub mul : Bounds F → Bounds F → m (Option (Bounds F)))
    (bubble : Bounds F) : Polynomial C → m (Option (HardwareAffine.Form F)) :=
  eval constant input (HardwareAffine.combine add) (HardwareAffine.combine sub)
    (HardwareAffine.product sub mul bubble)

inductive Result (F : Type) where
  | unknown
  | conflict
  | bound : Bounds F → Result F
  deriving Repr

/-- Failure of either track preserves the other. A failed intersection is an
explicit conflict and MUST NOT fall back to either conflicting enclosure. -/
def merge {F : Type} (lt : F → F → Bool) (mn mx : F → F → F)
    (ordinary affine : Option (Bounds F)) : Result F :=
  match ordinary, affine with
  | none, none => .unknown
  | some I, none => .bound I
  | none, some J => .bound J
  | some I, some J => match HardwareQuadrants.clip lt mn mx I J with
    | none => .conflict
    | some K => .bound K

/-- Both tracks execute independently, even if the first fails. Combination is
at the root, without discarding the shared-parameter forms inside the tree. -/
def run {C F : Type} {m : Type → Type} [Monad m]
    (ordinary : Polynomial C → m (Option (Bounds F)))
    (affine : Polynomial C → m (Option (HardwareAffine.Form F)))
    (lt : F → F → Bool) (mn mx : F → F → F) (e : Polynomial C) : m (Result F) := do
  let I ← ordinary e
  let J ← affine e
  return merge lt mn mx I (J.map (HardwareAffine.hull mn mx))

end GeneralizedIntervalArithmetic.HardwareEvaluator
