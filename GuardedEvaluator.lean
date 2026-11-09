import DomainEvaluator
import LinearDivision

namespace GeneralizedIntervalArithmetic

private def combineGuarded (a b : Option LinearInterval)
    (op : LinearInterval → LinearInterval → Option LinearInterval) : Option LinearInterval := do
  let I ← a
  let J ← b
  op I J

/-- Shared-parameter arithmetic with whole-hull guarded division. A failed child
or denominator guard yields unknown; no algebraic simplification bypasses it. -/
def evalGuarded (X Y : LinearInterval) : Expr → Option LinearInterval
  | .const q => some (.exact ⟨q,q⟩)
  | .x => some X
  | .y => some Y
  | .add a b => combineLinear (evalGuarded X Y a) (evalGuarded X Y b) LinearInterval.add
  | .sub a b => combineLinear (evalGuarded X Y a) (evalGuarded X Y b) LinearInterval.sub
  | .mul a b => combineLinear (evalGuarded X Y a) (evalGuarded X Y b) LinearInterval.mul
  | .div a b => combineGuarded (evalGuarded X Y a) (evalGuarded X Y b) LinearInterval.div?

private theorem pure_some {a b : Option LinearInterval}
    {op : LinearInterval → LinearInterval → LinearInterval} {R : LinearInterval}
    (h : combineLinear a b op = some R) :
    ∃ I J, a = some I ∧ b = some J ∧ op I J = R := by
  cases a with
  | none => simp [combineLinear] at h
  | some I =>
    cases b with
    | none => simp [combineLinear] at h
    | some J => exact ⟨I,J,rfl,rfl,Option.some.inj h⟩

private theorem guarded_some {a b : Option LinearInterval}
    {op : LinearInterval → LinearInterval → Option LinearInterval} {R : LinearInterval}
    (h : combineGuarded a b op = some R) :
    ∃ I J, a = some I ∧ b = some J ∧ op I J = some R := by
  cases a with
  | none => simp [combineGuarded] at h
  | some I =>
    cases b with
    | none => simp [combineGuarded] at h
    | some J => exact ⟨I,J,rfl,rfl,h⟩

theorem evalGuarded_sound {X Y R : LinearInterval} {t x y z : ℝ} {e : Expr}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hv : Value x y e z) (hr : evalGuarded X Y e = some R) : R.Contains t z := by
  induction hv generalizing R with
  | const q =>
    cases Option.some.inj hr
    change (1-t)*(q:ℝ)+t*q ≤ q ∧ (q:ℝ) ≤ (1-t)*q+t*q
    have h : (1-t)*(q:ℝ)+t*q = q := by ring
    simp [h]
  | x => cases Option.some.inj hr; exact hx
  | y => cases Option.some.inj hr; exact hy
  | add ha hb iha ihb =>
    obtain ⟨I,J,hi,hj,rfl⟩ := pure_some hr
    exact linear_add_encloses (iha hi) (ihb hj)
  | sub ha hb iha ihb =>
    obtain ⟨I,J,hi,hj,rfl⟩ := pure_some hr
    exact linear_sub_encloses (iha hi) (ihb hj)
  | mul ha hb iha ihb =>
    obtain ⟨I,J,hi,hj,rfl⟩ := pure_some hr
    exact linear_mul_encloses ht (iha hi) (ihb hj)
  | div ha hb hn iha ihb =>
    obtain ⟨I,J,hi,hj,hdiv⟩ := guarded_some hr
    exact linear_div_encloses hdiv ht (iha hi) (ihb hj)

/-- Unlike polynomial definedness, guarded definedness is local to the certified
parameter and coordinate enclosures. Every division supplies its nonzero proof. -/
theorem evalGuarded_defined {X Y R : LinearInterval} {e : Expr} {t x y : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hr : evalGuarded X Y e = some R) : ∃ z, Value x y e z := by
  induction e generalizing R with
  | const q => exact ⟨q,Value.const q⟩
  | x => exact ⟨x,Value.x⟩
  | y => exact ⟨y,Value.y⟩
  | add a b iha ihb =>
    obtain ⟨I,J,hi,hj,_⟩ := pure_some hr
    obtain ⟨u,hu⟩ := iha hi
    obtain ⟨v,hv⟩ := ihb hj
    exact ⟨u+v,Value.add hu hv⟩
  | sub a b iha ihb =>
    obtain ⟨I,J,hi,hj,_⟩ := pure_some hr
    obtain ⟨u,hu⟩ := iha hi
    obtain ⟨v,hv⟩ := ihb hj
    exact ⟨u-v,Value.sub hu hv⟩
  | mul a b iha ihb =>
    obtain ⟨I,J,hi,hj,_⟩ := pure_some hr
    obtain ⟨u,hu⟩ := iha hi
    obtain ⟨v,hv⟩ := ihb hj
    exact ⟨u*v,Value.mul hu hv⟩
  | div a b iha ihb =>
    obtain ⟨I,J,hi,hj,hdiv⟩ := guarded_some hr
    obtain ⟨u,hu⟩ := iha hi
    obtain ⟨v,hv⟩ := ihb hj
    have hvJ := evalGuarded_sound ht hx hy hv hj
    exact ⟨u/v,Value.div hu hv (linear_div_nonzero hdiv ht hvJ)⟩

/-- Compatibility is exact on every successful old interpretation, not just a
claim that both results happen to enclose the same semantic values. -/
theorem evalGuarded_extends_polynomial {X Y R : LinearInterval} {e : Expr}
    (hr : evalLinear X Y e = some R) : evalGuarded X Y e = some R := by
  induction e generalizing R with
  | const q => exact hr
  | x => exact hr
  | y => exact hr
  | add a b iha ihb =>
    obtain ⟨I,J,hi,hj,rfl⟩ := pure_some hr
    simp [evalGuarded, iha hi, ihb hj, combineLinear]
  | sub a b iha ihb =>
    obtain ⟨I,J,hi,hj,rfl⟩ := pure_some hr
    simp [evalGuarded, iha hi, ihb hj, combineLinear]
  | mul a b iha ihb =>
    obtain ⟨I,J,hi,hj,rfl⟩ := pure_some hr
    simp [evalGuarded, iha hi, ihb hj, combineLinear]
  | div a b iha ihb => cases hr

theorem evalGuarded_relational_sound {X Y R : LinearInterval} {D E : DomainBounds ℝ}
    {A B : ℝ → ℝ → Prop} {e : Expr}
    (hX : (X.onDomain D).Sound A) (hY : (Y.onDomain E).Sound B)
    (hr : evalGuarded X Y e = some R) :
    (R.onDomain (D.inter E)).Sound (ExpressionValues A B e) := by
  refine ⟨?_,?_,?_⟩
  · rintro t z ⟨x,y,hx,hy,hv⟩
    exact evalGuarded_sound (hX.2.1 t x hx).1 (hX.1 t x hx) (hY.1 t y hy) hv hr
  · rintro t z ⟨x,y,hx,hy,_⟩
    exact ⟨(hX.2.1 t x hx).1,(hX.2.1 t x hx).2,(hY.2.1 t y hy).2⟩
  · intro t ht
    obtain ⟨x,hx⟩ := hX.2.2 t ⟨ht.1,ht.2.1⟩
    obtain ⟨y,hy⟩ := hY.2.2 t ⟨ht.1,ht.2.2⟩
    obtain ⟨z,hz⟩ := evalGuarded_defined ht.1 (hX.1 t x hx) (hY.1 t y hy) hr
    exact ⟨z,x,y,hx,hy,hz⟩

theorem evalGuarded_local_sound {X Y R : LinearInterval} {e : Expr} {x y : ℝ → ℝ}
    (D : ℝ → Prop) (hx : ∀ t ∈ Set.Icc (0:ℝ) 1, D t → X.Contains t (x t))
    (hy : ∀ t ∈ Set.Icc (0:ℝ) 1, D t → Y.Contains t (y t))
    (hr : evalGuarded X Y e = some R) :
    (R.partial.restrict D).Sound
      (fun t z => D t ∧ t ∈ Set.Icc (0:ℝ) 1 ∧ Value (x t) (y t) e z) := by
  refine ⟨?_,fun _ _ h => ⟨h.1,h.2.1⟩,?_⟩
  · rintro t z ⟨hD,ht,hv⟩
    exact evalGuarded_sound ht (hx t ht hD) (hy t ht hD) hv hr
  · intro t ht
    obtain ⟨z,hz⟩ := evalGuarded_defined ht.2 (hx t ht.2 ht.1) (hy t ht.2 ht.1) hr
    exact ⟨z,ht.1,ht.2,hz⟩

end GeneralizedIntervalArithmetic
