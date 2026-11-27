import IntervalDotProduct
import HardwareSine
import Mathlib.Algebra.BigOperators.Fin

/-! Fixed left-to-right multiply-then-add interval evaluation. Successful
outcomes enclose exact real dot products under existing operation contracts.
This pure program is not a verified native IO/FFI adapter. -/
namespace GeneralizedIntervalArithmetic.DirectedDotProduct
open HardwareAddition HardwareIntervalOps

/-- Process coordinate zero, then the remaining coordinates, without reassociation
or fused operations. A failed multiplication or addition returns none. -/
def loop {F : Type}
    (add mul : Bounds F → Bounds F → Option (Bounds F)) (acc : Bounds F) :
    {n : ℕ} → (Fin n → Bounds F) → (Fin n → Bounds F) → Option (Bounds F)
  | 0, _, _ => some acc
  | n+1, I, J => do
    let p ← mul (I 0) (J 0)
    let s ← add acc p
    loop add mul s (fun i : Fin n => I i.succ) (fun i => J i.succ)

def run {F : Type} (add mul : Bounds F → Bounds F → Option (Bounds F))
    (zero : F) {n : ℕ} (I J : Fin n → Bounds F) : Option (Bounds F) :=
  loop add mul ⟨zero,zero⟩ I J

/-- No tightness or exact rounding premise. The accumulator may already be wide. -/
theorem loop_encloses {F : Type} {decode : F → Option ℝ}
    {add mul : Bounds F → Bounds F → Option (Bounds F)}
    (ha : OpSound decode add (· + ·)) (hm : OpSound decode mul (· * ·))
    {n : ℕ} {I J : Fin n → Bounds F} {x y : Fin n → ℝ}
    {acc O : Bounds F} {a : ℝ} (hacc : Contains decode acc a)
    (hx : ∀ i, Contains decode (I i) (x i))
    (hy : ∀ i, Contains decode (J i) (y i))
    (hr : loop add mul acc I J = some O) :
    Contains decode O (a + IntervalDotProduct.dot x y) := by
  induction n generalizing a acc O with
  | zero =>
    simp only [loop,Option.some.injEq] at hr
    subst O
    simpa [IntervalDotProduct.dot] using hacc
  | succ n ih =>
    simp only [loop] at hr
    cases hp : mul (I 0) (J 0) with
    | none => simp [hp] at hr
    | some p =>
      cases hs : add acc p with
      | none => simp [hp,hs] at hr
      | some s =>
        have hr' : loop add mul s (fun i : Fin n => I i.succ)
            (fun i => J i.succ) = some O := by simpa [hp,hs] using hr
        have h := ih (ha _ _ _ _ _ hs hacc (hm _ _ _ _ _ hp (hx 0) (hy 0)))
          (fun i => hx i.succ) (fun i => hy i.succ) hr'
        simpa [IntervalDotProduct.dot,Fin.sum_univ_succ,add_assoc] using h

theorem run_encloses {F : Type} {decode : F → Option ℝ}
    {add mul : Bounds F → Bounds F → Option (Bounds F)}
    (ha : OpSound decode add (· + ·)) (hm : OpSound decode mul (· * ·))
    {zero : F} (hz : decode zero = some 0)
    {n : ℕ} {I J : Fin n → Bounds F} {x y : Fin n → ℝ} {O : Bounds F}
    (hx : ∀ i, Contains decode (I i) (x i))
    (hy : ∀ i, Contains decode (J i) (y i))
    (hr : run add mul zero I J = some O) :
    Contains decode O (IntervalDotProduct.dot x y) := by
  have hzero : Contains decode (⟨zero,zero⟩ : Bounds F) 0 :=
    ⟨0,0,hz,hz,le_rfl,le_rfl⟩
  simpa using loop_encloses ha hm hzero hx hy hr

/-- Existing paired-bound scalar calls and four-corner selection, unchanged. -/
def primitiveRun {F : Type}
    (addCall mulCall : F → F → Option (F × F)) (mn mx : F → F → F)
    (zero : F) {n : ℕ} (I J : Fin n → Bounds F) : Option (Bounds F) :=
  run (fun A B => assemble (addCall A.lo B.lo) (addCall A.hi B.hi))
    (fun A B => HardwareMultiplication.assembleFour mn mx
      (mulCall A.lo B.lo) (mulCall A.lo B.hi)
      (mulCall A.hi B.lo) (mulCall A.hi B.hi)) zero I J

/-- Discharges the generic premises using the already approved directed
addition/multiplication and finite min/max contracts. It does not assert success. -/
theorem primitiveRun_encloses {F : Type} {decode : F → Option ℝ}
    {addCall mulCall : F → F → Option (F × F)} {mn mx : F → F → F}
    (ha : ∀ a b, HardwareAddition.CallSound decode a b (addCall a b))
    (hm : ∀ a b, HardwareMultiplication.CallSound decode a b (mulCall a b))
    (hmin : HardwareMultiplication.SelectSound decode mn min)
    (hmax : HardwareMultiplication.SelectSound decode mx max)
    {zero : F} (hz : decode zero = some 0)
    {n : ℕ} {I J : Fin n → Bounds F} {x y : Fin n → ℝ} {O : Bounds F}
    (hx : ∀ i, Contains decode (I i) (x i))
    (hy : ∀ i, Contains decode (J i) (y i))
    (hr : primitiveRun addCall mulCall mn mx zero I J = some O) :
    Contains decode O (IntervalDotProduct.dot x y) :=
  run_encloses (HardwareSine.add_op_sound ha)
    (HardwareSine.mul_op_sound hmin hmax hm) hz hx hy hr

theorem mul_failure {F : Type} (add mul : Bounds F → Bounds F → Option (Bounds F))
    (acc : Bounds F) {n : ℕ} (I J : Fin (n+1) → Bounds F)
    (h : mul (I 0) (J 0) = none) : loop add mul acc I J = none := by
  simp [loop,h]

theorem add_failure {F : Type} (add mul : Bounds F → Bounds F → Option (Bounds F))
    (acc p : Bounds F) {n : ℕ} (I J : Fin (n+1) → Bounds F)
    (hp : mul (I 0) (J 0) = some p) (h : add acc p = none) :
    loop add mul acc I J = none := by simp [loop,hp,h]

end GeneralizedIntervalArithmetic.DirectedDotProduct
