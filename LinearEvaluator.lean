import LinearMultiplication
import Evaluator

namespace GeneralizedIntervalArithmetic

def combineLinear (a b : Option LinearInterval)
    (op : LinearInterval → LinearInterval → LinearInterval) : Option LinearInterval := do
  let I ← a
  let J ← b
  return op I J

/-- Exact rational polynomial fragment. Division is unsupported, even when its
denominator might be nonzero; none is unknown, never a semantic undefinedness claim. -/
def evalLinear (X Y : LinearInterval) : Expr → Option LinearInterval
  | .const q => some (.exact ⟨q, q⟩)
  | .x => some X
  | .y => some Y
  | .add a b => combineLinear (evalLinear X Y a) (evalLinear X Y b) LinearInterval.add
  | .sub a b => combineLinear (evalLinear X Y a) (evalLinear X Y b) LinearInterval.sub
  | .mul a b => combineLinear (evalLinear X Y a) (evalLinear X Y b) LinearInterval.mul
  | .div _ _ => none

private theorem combineLinear_some {a b : Option LinearInterval}
    {op : LinearInterval → LinearInterval → LinearInterval} {R : LinearInterval}
    (h : combineLinear a b op = some R) :
    ∃ I J, a = some I ∧ b = some J ∧ op I J = R := by
  cases a with
  | none => simp [combineLinear] at h
  | some I =>
    cases b with
    | none => simp [combineLinear] at h
    | some J => exact ⟨I, J, rfl, rfl, Option.some.inj h⟩

theorem evalLinear_sound {X Y R : LinearInterval} {t x y z : ℝ} {e : Expr}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hv : Value x y e z) (hr : evalLinear X Y e = some R) : R.Contains t z := by
  induction hv generalizing R with
  | const q =>
    cases Option.some.inj hr
    change (1-t)*(q:ℝ)+t*q ≤ q ∧ (q:ℝ) ≤ (1-t)*q+t*q
    have h : (1-t)*(q:ℝ)+t*q = q := by ring
    simp [h]
  | x => cases Option.some.inj hr; exact hx
  | y => cases Option.some.inj hr; exact hy
  | add ha hb iha ihb =>
    obtain ⟨I, J, hi, hj, rfl⟩ := combineLinear_some hr
    exact linear_add_encloses (iha hi) (ihb hj)
  | sub ha hb iha ihb =>
    obtain ⟨I, J, hi, hj, rfl⟩ := combineLinear_some hr
    exact linear_sub_encloses (iha hi) (ihb hj)
  | mul ha hb iha ihb =>
    obtain ⟨I, J, hi, hj, rfl⟩ := combineLinear_some hr
    exact linear_mul_encloses ht (iha hi) (ihb hj)
  | div ha hb hn iha ihb => cases hr

/-- Successful interpretation certifies an actual partial-semantic value, not
just an enclosure conditional on an unproved existence premise. -/
theorem evalLinear_defined {X Y R : LinearInterval} {e : Expr}
    (hr : evalLinear X Y e = some R) (x y : ℝ) : ∃ z, Value x y e z := by
  induction e generalizing R with
  | const q => exact ⟨q, Value.const q⟩
  | x => exact ⟨x, Value.x⟩
  | y => exact ⟨y, Value.y⟩
  | add a b iha ihb =>
    obtain ⟨I, J, hi, hj, _⟩ := combineLinear_some hr
    obtain ⟨u, hu⟩ := iha hi
    obtain ⟨v, hv⟩ := ihb hj
    exact ⟨u+v, Value.add hu hv⟩
  | sub a b iha ihb =>
    obtain ⟨I, J, hi, hj, _⟩ := combineLinear_some hr
    obtain ⟨u, hu⟩ := iha hi
    obtain ⟨v, hv⟩ := ihb hj
    exact ⟨u-v, Value.sub hu hv⟩
  | mul a b iha ihb =>
    obtain ⟨I, J, hi, hj, _⟩ := combineLinear_some hr
    obtain ⟨u, hu⟩ := iha hi
    obtain ⟨v, hv⟩ := ihb hj
    exact ⟨u*v, Value.mul hu hv⟩
  | div a b iha ihb => cases hr

/-- Bridge into the existing domain contract on the certified parameter range. -/
theorem evalLinear_partial_sound {X Y R : LinearInterval} {e : Expr}
    {x y : ℝ → ℝ} (hx : ∀ t ∈ Set.Icc (0:ℝ) 1, X.Contains t (x t))
    (hy : ∀ t ∈ Set.Icc (0:ℝ) 1, Y.Contains t (y t))
    (hr : evalLinear X Y e = some R) :
    R.partial.Sound (fun t z => t ∈ Set.Icc (0:ℝ) 1 ∧ Value (x t) (y t) e z) := by
  refine ⟨?_, fun _ _ h => h.1, ?_⟩
  · rintro t z ⟨ht, hz⟩
    exact evalLinear_sound ht (hx t ht) (hy t ht) hz hr
  · intro t ht
    obtain ⟨z, hz⟩ := evalLinear_defined hr (x t) (y t)
    exact ⟨z, ht, hz⟩

/-- A caller's explicit parameter restriction is retained; no domain inference
for partial coordinate functions is performed by this interpreter. -/
theorem evalLinear_restricted_sound {X Y R : LinearInterval} {e : Expr}
    {x y : ℝ → ℝ} (hx : ∀ t ∈ Set.Icc (0:ℝ) 1, X.Contains t (x t))
    (hy : ∀ t ∈ Set.Icc (0:ℝ) 1, Y.Contains t (y t))
    (hr : evalLinear X Y e = some R) (D : ℝ → Prop) :
    (R.partial.restrict D).Sound
      (fun t z => D t ∧ t ∈ Set.Icc (0:ℝ) 1 ∧ Value (x t) (y t) e z) :=
  restrict_sound (evalLinear_partial_sound hx hy hr) D

theorem evalLinear_div_unknown (X Y : LinearInterval) (a b : Expr) :
    evalLinear X Y (.div a b) = none := rfl


/-- On constant inputs, every successful polynomial interpretation is exactly the
constant embedding of the ordinary exact interval evaluation. This is one-way:
division can succeed in eval while remaining unsupported by evalLinear. -/
theorem evalLinear_constant_correspondence (X Y : QInterval) {e : Expr}
    {R : LinearInterval}
    (hr : evalLinear (.constant X) (.constant Y) e = some R) :
    ∃ I, eval exactBackend X Y e = some I ∧ R = .constant I := by
  induction e generalizing R with
  | const q =>
    cases Option.some.inj hr
    exact ⟨.point q,rfl,rfl⟩
  | x =>
    cases Option.some.inj hr
    exact ⟨X,rfl,rfl⟩
  | y =>
    cases Option.some.inj hr
    exact ⟨Y,rfl,rfl⟩
  | add a b iha ihb =>
    obtain ⟨A,B,ha,hb,rfl⟩ := combineLinear_some hr
    obtain ⟨I,hi,rfl⟩ := iha ha
    obtain ⟨J,hj,rfl⟩ := ihb hb
    exact ⟨I.add J,by simp only [eval,hi,hj]; rfl,linear_constant_add I J⟩
  | sub a b iha ihb =>
    obtain ⟨A,B,ha,hb,rfl⟩ := combineLinear_some hr
    obtain ⟨I,hi,rfl⟩ := iha ha
    obtain ⟨J,hj,rfl⟩ := ihb hb
    exact ⟨I.sub J,by simp only [eval,hi,hj]; rfl,linear_constant_sub I J⟩
  | mul a b iha ihb =>
    obtain ⟨A,B,ha,hb,rfl⟩ := combineLinear_some hr
    obtain ⟨I,hi,rfl⟩ := iha ha
    obtain ⟨J,hj,rfl⟩ := ihb hb
    exact ⟨I.mul J,by simp only [eval,hi,hj]; rfl,linear_constant_mul I J⟩
  | div a b iha ihb => cases hr

end GeneralizedIntervalArithmetic
