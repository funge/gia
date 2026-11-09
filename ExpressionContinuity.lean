import Presence

namespace GeneralizedIntervalArithmetic

/-- A total real expression used only with a proved `Value` witness below.
Its division-by-zero values are never accepted as partial semantic values. -/
noncomputable def Expr.realValue (x y : ℝ) : Expr → ℝ
  | .const q => q
  | .x => x
  | .y => y
  | .add a b => a.realValue x y + b.realValue x y
  | .sub a b => a.realValue x y - b.realValue x y
  | .mul a b => a.realValue x y * b.realValue x y
  | .div a b => a.realValue x y / b.realValue x y

theorem value_eq_realValue {x y z : ℝ} {e : Expr} (h : Value x y e z) :
    z = e.realValue x y := by
  induction h <;> simp_all [Expr.realValue]

private theorem combine_some {a b : Option QInterval}
    {op : QInterval → QInterval → Option QInterval} {R : QInterval}
    (h : combine a b op = some R) :
    ∃ I J, a = some I ∧ b = some J ∧ op I J = some R := by
  cases a with
  | none => simp [combine] at h
  | some I =>
    cases b with
    | none => simp [combine] at h
    | some J => exact ⟨I, J, rfl, rfl, h⟩

/-- Success of the interval evaluator certifies continuity and definedness along
every continuous curve contained in the input box. This includes division:
the successful denominator guard proves nonzero values throughout the curve. -/
theorem eval_curve_continuous {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {sx sy : ℝ → ℝ} {T : Set ℝ}
    (cx : ContinuousOn sx T) (cy : ContinuousOn sy T)
    (hx : ∀ t ∈ T, X.Contains (sx t)) (hy : ∀ t ∈ T, Y.Contains (sy t))
    (e : Expr) : ∀ R, eval B X Y e = some R →
    ContinuousOn (fun t => e.realValue (sx t) (sy t)) T ∧
    ∀ t ∈ T, Value (sx t) (sy t) e (e.realValue (sx t) (sy t)) := by
  induction e with
  | const q => exact fun _ _ => ⟨continuousOn_const, fun _ _ => Value.const q⟩
  | x => exact fun _ _ => ⟨cx, fun _ _ => Value.x⟩
  | y => exact fun _ _ => ⟨cy, fun _ _ => Value.y⟩
  | add a b iha ihb =>
    intro R hr
    obtain ⟨I, J, ha, hb, _⟩ := combine_some hr
    obtain ⟨ca, va⟩ := iha I ha
    obtain ⟨cb, vb⟩ := ihb J hb
    exact ⟨ca.add cb, fun t ht => Value.add (va t ht) (vb t ht)⟩
  | sub a b iha ihb =>
    intro R hr
    obtain ⟨I, J, ha, hb, _⟩ := combine_some hr
    obtain ⟨ca, va⟩ := iha I ha
    obtain ⟨cb, vb⟩ := ihb J hb
    exact ⟨ca.sub cb, fun t ht => Value.sub (va t ht) (vb t ht)⟩
  | mul a b iha ihb =>
    intro R hr
    obtain ⟨I, J, ha, hb, _⟩ := combine_some hr
    obtain ⟨ca, va⟩ := iha I ha
    obtain ⟨cb, vb⟩ := ihb J hb
    exact ⟨ca.mul cb, fun t ht => Value.mul (va t ht) (vb t ht)⟩
  | div a b iha ihb =>
    intro R hr
    obtain ⟨I, J, ha, hb, hop⟩ := combine_some hr
    obtain ⟨ca, va⟩ := iha I ha
    obtain ⟨cb, vb⟩ := ihb J hb
    have hn : ∀ t ∈ T, b.realValue (sx t) (sy t) ≠ 0 := by
      intro t ht
      exact guardedDiv_denominator_nonzero
        (eval_sound hB (hx t ht) (hy t ht) (vb t ht) J hb) hop
    exact ⟨ca.div cb hn, fun t ht => Value.div (va t ht) (vb t ht) (hn t ht)⟩

/-- A fully evaluator-certified presence theorem. Continuity and definedness
are derived from whole-box success, not postulated. Endpoint signs may come
from either the exact backend or any backend with proved enclosure contracts. -/
theorem evaluator_segment_presence {B : Backend} (hB : BackendSound B)
    {X Y R L U : QInterval} {e : Expr} {ax ay bx by_ : ℚ}
    (hax : X.Contains ax) (hay : Y.Contains ay)
    (hbx : X.Contains bx) (hby : Y.Contains by_)
    (hbox : eval B X Y e = some R)
    (hleft : eval B (.point ax) (.point ay) e = some L)
    (hright : eval B (.point bx) (.point by_) e = some U)
    (hn : L.hi ≤ 0) (hp : 0 ≤ U.lo) :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y e 0 := by
  obtain ⟨cg, vg⟩ := eval_curve_continuous hB
    (segment_continuous (ax : ℝ) bx).continuousOn
    (segment_continuous (ay : ℝ) by_).continuousOn
    (fun _ ht => segment_mem hax hbx ht) (fun _ ht => segment_mem hay hby ht) e R hbox
  apply segment_presence hax hay hbx hby cg vg
  · exact eval_sound hB (by simp [QInterval.Contains, QInterval.point])
      (by simp [QInterval.Contains, QInterval.point]) (vg 0 (by norm_num)) L hleft
  · exact eval_sound hB (by simp [QInterval.Contains, QInterval.point])
      (by simp [QInterval.Contains, QInterval.point]) (vg 1 (by norm_num)) U hright
  · exact hn
  · exact hp

end GeneralizedIntervalArithmetic
