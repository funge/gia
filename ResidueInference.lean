import IntegerResidue

namespace GeneralizedIntervalArithmetic.ResidueInference
open IntegerResidue

/-- A small proof-side syntax. Opaque leaves retain the client's partial relation. -/
inductive Expr (A : Type*) where
  | integer : ℤ → Expr A
  | atom : A → Expr A
  | floor : Expr A → Expr A
  | add : Expr A → Expr A → Expr A
  | sub : Expr A → Expr A → Expr A
  | scale : ℤ → Expr A → Expr A

def Value {A P : Type*} (R : A → P → ℝ → Prop) : Expr A → P → ℝ → Prop
  | .integer n, _, z => z = n
  | .atom a, p, z => R a p z
  | .floor e, p, z => ∃ x, Value R e p x ∧ z = (⌊x⌋ : ℤ)
  | .add e f, p, z => ∃ x y, Value R e p x ∧ Value R f p y ∧ z = x+y
  | .sub e f, p, z => ∃ x y, Value R e p x ∧ Value R f p y ∧ z = x-y
  | .scale a e, p, z => ∃ x, Value R e p x ∧ z = a*x

def integer : Expr A → Bool
  | .integer _ => true
  | .atom _ => false
  | .floor _ => true
  | .add e f | .sub e f => integer e && integer f
  | .scale _ e => integer e

theorem integer_sound {A P : Type*} (R : A → P → ℝ → Prop) (e : Expr A)
    (h : integer e = true) {p z} (hz : Value R e p z) : IntegerValue z := by
  induction e generalizing z with
  | integer n => exact ⟨n,hz⟩
  | atom a => simp [integer] at h
  | floor e ih => obtain ⟨x,_,rfl⟩ := hz; exact floor_integer x
  | add e f ih jh =>
    obtain ⟨x,y,hx,hy,rfl⟩ := hz
    simp only [integer, Bool.and_eq_true] at h
    exact integer_add (ih h.1 hx) (jh h.2 hy)
  | sub e f ih jh =>
    obtain ⟨x,y,hx,hy,rfl⟩ := hz
    simp only [integer, Bool.and_eq_true] at h
    exact integer_sub (ih h.1 hx) (jh h.2 hy)
  | scale a e ih =>
    obtain ⟨x,hx,rfl⟩ := hz
    exact integer_scale a (ih h hx)

/-- Infer a residue for a requested modulus. None is lack of evidence, not emptiness. -/
def infer (d : ℤ) : Expr A → Option ℤ
  | .integer n => some n
  | .atom _ => none
  | .floor _ => if d = 1 then some 0 else none
  | .add e f => do return (← infer d e) + (← infer d f)
  | .sub e f => do return (← infer d e) - (← infer d f)
  | .scale a e =>
    if d ∣ a ∧ integer e = true then some 0
    else (infer d e).map (a*·)

theorem infer_sound {A P : Type*} (R : A → P → ℝ → Prop) (d : ℤ) (e : Expr A)
    {r : ℤ} (h : infer d e = some r) {p z} (hz : Value R e p z) : HasResidue d r z := by
  induction e generalizing r z with
  | integer n =>
    simp only [infer, Option.some.injEq] at h
    subst r
    exact ⟨0,by simpa using hz⟩
  | atom a => simp [infer] at h
  | floor e ih =>
    obtain ⟨x,_,rfl⟩ := hz
    by_cases hd : d=1
    · subst d; simp [infer] at h; subst r; exact ⟨⌊x⌋,by simp⟩
    · simp [infer,hd] at h
  | add e f ih jh =>
    obtain ⟨x,y,hx,hy,rfl⟩ := hz
    cases he : infer d e <;> cases hf : infer d f <;> simp [infer,he,hf] at h
    subst r
    exact residue_add (ih he hx) (jh hf hy)
  | sub e f ih jh =>
    obtain ⟨x,y,hx,hy,rfl⟩ := hz
    cases he : infer d e <;> cases hf : infer d f <;> simp [infer,he,hf] at h
    subst r
    exact residue_sub (ih he hx) (jh hf hy)
  | scale a e ih =>
    obtain ⟨x,hx,rfl⟩ := hz
    by_cases hc : d ∣ a ∧ integer e = true
    · simp [infer,hc] at h; subst r
      simpa using affine_residue (integer_sound R e hc.2 hx) a 0 d 0 hc.1 (dvd_zero d)
    · cases he : infer d e <;> simp [infer,hc,he] at h
      subst r
      exact residue_scale a (ih he hx)

/-- Inference and bounds refer to the same actual value and parameter. -/
theorem exclude {A P : Type*} (R : A → P → ℝ → Prop) (e : Expr A)
    {d r : ℤ} (hd : 0 < d) (hi : infer d e = some r) {p : P} {L U : ℝ}
    (gap : ⌊(U-r)/d⌋ < ⌈(L-r)/d⌉) : ¬ ∃ z, Value R e p z ∧ L ≤ z ∧ z ≤ U :=
  relation_exclusion hd (fun _ hz => infer_sound R d e hi hz) gap
theorem exclude_enclosure {A P : Type*} (R : A → P → ℝ → Prop) (e : Expr A)
    {I : PartialEnclosure P} (hs : I.Sound (Value R e))
    {d r : ℤ} (hd : 0 < d) (hi : infer d e = some r) {p : P} {L U : ℝ}
    (gap : ⌊(min U (I.values.upper p)-r)/d⌋ <
      ⌈(max L (I.values.lower p)-r)/d⌉) :
    ¬ ∃ z, Value R e p z ∧ L ≤ z ∧ z ≤ U :=
  enclosure_window_exclusion hs hd (fun _ hz => infer_sound R d e hi hz) gap

end GeneralizedIntervalArithmetic.ResidueInference
