import IntervalOps

namespace GeneralizedIntervalArithmetic

inductive Expr where
  | const : ℚ → Expr
  | x | y
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr

/-- Partial real semantics: a division value requires a nonzero denominator.
There is no semantic value assigned to division by zero. -/
inductive Value (x y : ℝ) : Expr → ℝ → Prop where
  | const (q : ℚ) : Value x y (.const q) q
  | x : Value x y .x x
  | y : Value x y .y y
  | add {a b u v} : Value x y a u → Value x y b v → Value x y (.add a b) (u+v)
  | sub {a b u v} : Value x y a u → Value x y b v → Value x y (.sub a b) (u-v)
  | mul {a b u v} : Value x y a u → Value x y b v → Value x y (.mul a b) (u*v)
  | div {a b u v} : Value x y a u → Value x y b v → v ≠ 0 →
      Value x y (.div a b) (u/v)

/-- A backend may widen exact bounds, or decline with `none` (unknown). -/
abbrev Backend := QInterval → Option QInterval

def BackendSound (B : Backend) : Prop :=
  ∀ I R z, B I = some R → I.Contains z → R.Contains z

def exactBackend : Backend := some

theorem exactBackend_sound : BackendSound exactBackend := by
  intro I R z h hz
  cases h
  exact hz

def combine (a b : Option QInterval)
    (op : QInterval → QInterval → Option QInterval) : Option QInterval := do
  let I ← a
  let J ← b
  op I J

def guardedDiv (B : Backend) (I J : QInterval) : Option QInterval :=
  if h : J.AwayZero then B (I.mul (J.recip h)) else none

def eval (B : Backend) (X Y : QInterval) : Expr → Option QInterval
  | .const q => B (.point q)
  | .x => some X
  | .y => some Y
  | .add a b => combine (eval B X Y a) (eval B X Y b) (fun I J => B (I.add J))
  | .sub a b => combine (eval B X Y a) (eval B X Y b) (fun I J => B (I.sub J))
  | .mul a b => combine (eval B X Y a) (eval B X Y b) (fun I J => B (I.mul J))
  | .div a b => combine (eval B X Y a) (eval B X Y b) (guardedDiv B)

private theorem combine_sound {a b : Option QInterval} {x y z : ℝ}
    {op : QInterval → QInterval → Option QInterval}
    (ha : ∀ I, a = some I → I.Contains x)
    (hb : ∀ J, b = some J → J.Contains y)
    (hop : ∀ I J R, I.Contains x → J.Contains y → op I J = some R → R.Contains z)
    {R : QInterval} (hr : combine a b op = some R) : R.Contains z := by
  cases a with
  | none => simp [combine] at hr
  | some I =>
    cases b with
    | none => simp [combine] at hr
    | some J => exact hop I J R (ha I rfl) (hb J rfl) hr

theorem guardedDiv_sound {B : Backend} (hB : BackendSound B)
    {I J R : QInterval} {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y)
    (hr : guardedDiv B I J = some R) : R.Contains (x/y) := by
  unfold guardedDiv at hr
  split at hr
  · rename_i h
    exact hB _ _ _ hr (by simpa [div_eq_mul_inv] using mul_encloses hx (recip_encloses h hy))
  · simp at hr

theorem guardedDiv_denominator_nonzero {B : Backend} {I J R : QInterval} {y : ℝ}
    (hy : J.Contains y) (hr : guardedDiv B I J = some R) : y ≠ 0 := by
  unfold guardedDiv at hr
  split at hr
  · rename_i h
    exact awayZero_nonzero h hy
  · simp at hr

/-- The same structural proof serves exact and sound outward-rounding backends.
It quantifies over defined real values, not Lean's totalized expression division. -/
theorem eval_sound {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {x y : ℝ} (hx : X.Contains x) (hy : Y.Contains y)
    {e : Expr} {z : ℝ} (hv : Value x y e z) :
    ∀ R, eval B X Y e = some R → R.Contains z := by
  induction hv with
  | const q => exact fun R hr => hB _ R _ hr ⟨le_rfl, le_rfl⟩
  | x => intro R hr; cases hr; exact hx
  | y => intro R hr; cases hr; exact hy
  | add ha hb iha ihb =>
    exact fun _ hr => combine_sound iha ihb
      (fun _ _ _ ha hb hr => hB _ _ _ hr (add_encloses ha hb)) hr
  | sub ha hb iha ihb =>
    exact fun _ hr => combine_sound iha ihb
      (fun _ _ _ ha hb hr => hB _ _ _ hr (sub_encloses ha hb)) hr
  | mul ha hb iha ihb =>
    exact fun _ hr => combine_sound iha ihb
      (fun _ _ _ ha hb hr => hB _ _ _ hr (mul_encloses ha hb)) hr
  | div ha hb hn iha ihb =>
    exact fun _ hr => combine_sound iha ihb
      (fun _ _ _ ha hb hr => guardedDiv_sound hB ha hb hr) hr

def classifyExpr (B : Backend) (X Y : QInterval) (e : Expr) : Classification :=
  match eval B X Y e with
  | none => .unknown
  | some R => classify R

theorem eval_empty_pixel {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {e : Expr} (hc : classifyExpr B X Y e = .empty) :
    ¬ ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y e 0 := by
  rintro ⟨x, y, hx, hy, hv⟩
  unfold classifyExpr at hc
  cases hr : eval B X Y e with
  | none => simp [hr] at hc
  | some R =>
    simp only [hr] at hc
    exact classify_empty_sound hc (eval_sound hB hx hy hv R hr) rfl

/-- A denominator interval containing zero always makes this division unknown,
even if the expression has defined values at some or all points. -/
theorem guardedDiv_zero_unknown (B : Backend) (I J : QInterval)
    (h : J.lo ≤ 0 ∧ 0 ≤ J.hi) : guardedDiv B I J = none := by
  simp [guardedDiv, QInterval.AwayZero, not_lt_of_ge h.1, not_lt_of_ge h.2]

end GeneralizedIntervalArithmetic
