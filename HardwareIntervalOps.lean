import HardwareAddition

namespace GeneralizedIntervalArithmetic.HardwareIntervalOps
open HardwareAddition

/-- Successful interval operations enclose the corresponding real operation.
Existing directed-primitive assembly proofs discharge this contract. -/
def OpSound {F : Type} (decode : F → Option ℝ)
    (op : Bounds F → Bounds F → Option (Bounds F)) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ I J O x y, op I J = some O → Contains decode I x → Contains decode J y →
    Contains decode O (f x y)

end GeneralizedIntervalArithmetic.HardwareIntervalOps
