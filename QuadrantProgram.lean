import SineProgram

namespace GeneralizedIntervalArithmetic.HardwareQuadrants
open HardwareAddition

inductive Mode where
  | sin | cos | negSin | negCos
  deriving DecidableEq, Repr

structure Cell (F : Type) where
  domain : Bounds F
  coefficient : F
  mode : Mode

/-- Finite constant table: no runtime rational arithmetic or integer conversion. -/
inductive Mark where
  | neg4 | neg375 | neg225 | neg075 | pos075 | pos225 | pos375 | pos4
  | neg15 | neg1 | neg05 | zero | pos05 | pos1 | pos15
  deriving DecidableEq, Repr

def table {F : Type} (v : Mark → F) : List (Cell F) :=
  [⟨⟨v .neg4, v .neg375⟩, v .neg15, .cos⟩,
   ⟨⟨v .neg375, v .neg225⟩, v .neg1, .negSin⟩,
   ⟨⟨v .neg225, v .neg075⟩, v .neg05, .negCos⟩,
   ⟨⟨v .neg075, v .pos075⟩, v .zero, .sin⟩,
   ⟨⟨v .pos075, v .pos225⟩, v .pos05, .cos⟩,
   ⟨⟨v .pos225, v .pos375⟩, v .pos1, .negSin⟩,
   ⟨⟨v .pos375, v .pos4⟩, v .pos15, .negCos⟩]

def clip {F : Type} (lt : F → F → Bool) (mn mx : F → F → F)
    (I J : Bounds F) : Option (Bounds F) :=
  let K : Bounds F := ⟨mx I.lo J.lo, mn I.hi J.hi⟩
  if lt K.hi K.lo then none else some K

def hull {F : Type} (mn mx : F → F → F) (I J : Bounds F) : Bounds F :=
  ⟨mn I.lo J.lo, mx I.hi J.hi⟩

def hullList {F : Type} (mn mx : F → F → F) : List (Bounds F) → Option (Bounds F)
  | [] => none
  | I :: rest => match hullList mn mx rest with
    | none => some I
    | some J => some (hull mn mx I J)

def evaluate {F : Type} {m : Type → Type} [Monad m]
    (mul sub : Bounds F → Bounds F → m (Option (Bounds F)))
    (sin cos : Bounds F → m (Option (Bounds F))) (zero : F)
    (pi : Bounds F) (cell : Cell F) (I : Bounds F) : m (Option (Bounds F)) := do
  let some shift ← mul ⟨cell.coefficient, cell.coefficient⟩ pi | return none
  let some residual ← sub I shift | return none
  match cell.mode with
  | .sin => sin residual
  | .cos => cos residual
  | .negSin =>
    let some O ← sin residual | return none
    sub ⟨zero,zero⟩ O
  | .negCos =>
    let some O ← cos residual | return none
    sub ⟨zero,zero⟩ O

/-- An empty intersection is skipped. Any evaluation failure aborts the whole
cover; it must not be mistaken for an empty intersection. -/
def pieces {F : Type} {m : Type → Type} [Monad m]
    (lt : F → F → Bool) (mn mx : F → F → F)
    (eval : Cell F → Bounds F → m (Option (Bounds F)))
    (I : Bounds F) : List (Cell F) → m (Option (List (Bounds F)))
  | [] => pure (some [])
  | c :: cs => do
    match clip lt mn mx I c.domain with
    | none => pieces lt mn mx eval I cs
    | some J =>
      let some O ← eval c J | return none
      let some rest ← pieces lt mn mx eval I cs | return none
      return some (O :: rest)

def run {F : Type} {m : Type → Type} [Monad m]
    (supported : Bounds F → Bool) (lt : F → F → Bool) (mn mx : F → F → F)
    (eval : Cell F → Bounds F → m (Option (Bounds F)))
    (cs : List (Cell F)) (I : Bounds F) : m (Option (Bounds F)) := do
  if !supported I then return none
  let some outputs ← pieces lt mn mx eval I cs | return none
  return hullList mn mx outputs

end GeneralizedIntervalArithmetic.HardwareQuadrants
