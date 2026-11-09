import Evaluator

namespace GeneralizedIntervalArithmetic

/-- Optional finite endpoint rounding. A failed conversion is unknown.
This is an adapter, not an IEEE 754 rounding implementation. -/
def directedBackend (down up : ℚ → Option ℚ) : Backend := fun I => do
  let lo ← down I.lo
  let hi ← up I.hi
  if h : lo ≤ hi then some ⟨lo, hi, h⟩ else none

/-- Exactly the outward endpoint contracts used in the previous milestone,
conditional on successful finite results. No global finite-output assumption. -/
theorem directedBackend_sound (down up : ℚ → Option ℚ)
    (hd : ∀ q r, down q = some r → r ≤ q)
    (hu : ∀ q r, up q = some r → q ≤ r) :
    BackendSound (directedBackend down up) := by
  intro I R z hr hz
  cases hl : down I.lo with
  | none => simp [directedBackend, hl] at hr
  | some lo =>
    cases hh : up I.hi with
    | none => simp [directedBackend, hl, hh] at hr
    | some hi =>
      simp only [directedBackend, hl, hh, Option.bind_some] at hr
      change (if h : lo ≤ hi then some (QInterval.mk lo hi h) else none) = some R at hr
      split at hr
      · cases hr
        have hlo : (lo : ℝ) ≤ I.lo := by exact_mod_cast hd _ _ hl
        have hhi : (I.hi : ℝ) ≤ hi := by exact_mod_cast hu _ _ hh
        exact ⟨hlo.trans hz.1, hz.2.trans hhi⟩
      · simp at hr

theorem eval_exact_sound {X Y : QInterval} {x y : ℝ}
    (hx : X.Contains x) (hy : Y.Contains y) {e : Expr} {z : ℝ}
    (hv : Value x y e z) {R : QInterval} (hr : eval exactBackend X Y e = some R) :
    R.Contains z := eval_sound exactBackend_sound hx hy hv R hr

theorem eval_directed_sound (down up : ℚ → Option ℚ)
    (hd : ∀ q r, down q = some r → r ≤ q)
    (hu : ∀ q r, up q = some r → q ≤ r)
    {X Y : QInterval} {x y : ℝ} (hx : X.Contains x) (hy : Y.Contains y)
    {e : Expr} {z : ℝ} (hv : Value x y e z) {R : QInterval}
    (hr : eval (directedBackend down up) X Y e = some R) : R.Contains z :=
  eval_sound (directedBackend_sound down up hd hu) hx hy hv R hr

theorem directed_empty_pixel (down up : ℚ → Option ℚ)
    (hd : ∀ q r, down q = some r → r ≤ q)
    (hu : ∀ q r, up q = some r → q ≤ r)
    {X Y : QInterval} {e : Expr}
    (hc : classifyExpr (directedBackend down up) X Y e = .empty) :
    ¬ ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y e 0 :=
  eval_empty_pixel (directedBackend_sound down up hd hu) hc

end GeneralizedIntervalArithmetic
