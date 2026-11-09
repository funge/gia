import DomainQueries

namespace GeneralizedIntervalArithmetic

private theorem combine_success {a b : Option QInterval}
    {op : QInterval → QInterval → Option QInterval} {R : QInterval}
    (hr : combine a b op = some R) :
    ∃ I J, a = some I ∧ b = some J ∧ op I J = some R := by
  cases a with
  | none => simp [combine] at hr
  | some I =>
    cases b with
    | none => simp [combine] at hr
    | some J => exact ⟨I, J, rfl, rfl, hr⟩

/-- Successful interval evaluation supplies an actual partial value at every
input enclosed by the input intervals. Soundness of the backend is explicit. -/
theorem eval_defined {B : Backend} (hB : BackendSound B)
    {X Y R : QInterval} {x y : ℝ} (hx : X.Contains x) (hy : Y.Contains y)
    {e : Expr} (hr : eval B X Y e = some R) : ∃ z, Value x y e z := by
  induction e generalizing R with
  | const q => exact ⟨q, Value.const q⟩
  | x => exact ⟨x, Value.x⟩
  | y => exact ⟨y, Value.y⟩
  | add a b iha ihb =>
    obtain ⟨I, J, ha, hb, _⟩ := combine_success hr
    obtain ⟨u, hu⟩ := iha ha
    obtain ⟨v, hv⟩ := ihb hb
    exact ⟨u+v, Value.add hu hv⟩
  | sub a b iha ihb =>
    obtain ⟨I, J, ha, hb, _⟩ := combine_success hr
    obtain ⟨u, hu⟩ := iha ha
    obtain ⟨v, hv⟩ := ihb hb
    exact ⟨u-v, Value.sub hu hv⟩
  | mul a b iha ihb =>
    obtain ⟨I, J, ha, hb, _⟩ := combine_success hr
    obtain ⟨u, hu⟩ := iha ha
    obtain ⟨v, hv⟩ := ihb hb
    exact ⟨u*v, Value.mul hu hv⟩
  | div a b iha ihb =>
    obtain ⟨I, J, ha, hb, hd⟩ := combine_success hr
    obtain ⟨u, hu⟩ := iha ha
    obtain ⟨v, hv⟩ := ihb hb
    exact ⟨u/v, Value.div hu hv
      (guardedDiv_denominator_nonzero (eval_sound hB hx hy hv J hb) hd)⟩

/-- Completeness is restricted to the exact backend and rational singleton
coordinates. It does not hold for arbitrary enclosing intervals or backends. -/
theorem eval_point_complete {x y : ℚ} {e : Expr} {z : ℝ}
    (hv : Value (x:ℝ) (y:ℝ) e z) :
    ∃ r : ℚ, z = (r:ℝ) ∧ eval exactBackend (.point x) (.point y) e = some (.point r) := by
  induction hv with
  | const q => exact ⟨q, rfl, rfl⟩
  | x => exact ⟨x, rfl, rfl⟩
  | y => exact ⟨y, rfl, rfl⟩
  | add ha hb iha ihb =>
    obtain ⟨u, rfl, hu⟩ := iha
    obtain ⟨v, rfl, hv⟩ := ihb
    refine ⟨u+v, by simp, ?_⟩
    simp only [eval, hu, hv]
    simp [combine, exactBackend, QInterval.add, QInterval.point]
  | sub ha hb iha ihb =>
    obtain ⟨u, rfl, hu⟩ := iha
    obtain ⟨v, rfl, hv⟩ := ihb
    refine ⟨u-v, by simp, ?_⟩
    simp only [eval, hu, hv]
    simp [combine, exactBackend, QInterval.sub, QInterval.point]
  | mul ha hb iha ihb =>
    obtain ⟨u, rfl, hu⟩ := iha
    obtain ⟨v, rfl, hv⟩ := ihb
    refine ⟨u*v, by simp, ?_⟩
    simp only [eval, hu, hv]
    simp [combine, exactBackend, QInterval.mul, QInterval.point]
  | div ha hb hn iha ihb =>
    obtain ⟨u, rfl, hu⟩ := iha
    obtain ⟨v, rfl, hv⟩ := ihb
    have hnq : v ≠ 0 := by exact_mod_cast hn
    have hz : (QInterval.point v).AwayZero := lt_or_gt_of_ne hnq
    refine ⟨u/v, by simp, ?_⟩
    simp only [eval, hu, hv]
    change guardedDiv exactBackend (.point u) (.point v) = some (.point (u/v))
    rw [guardedDiv, dif_pos hz]
    simp [exactBackend, QInterval.mul, QInterval.recip, QInterval.point, div_eq_mul_inv]

theorem eval_point_defined_iff (x y : ℚ) (e : Expr) :
    (eval exactBackend (.point x) (.point y) e).isSome = true ↔
      ∃ z, Value (x:ℝ) (y:ℝ) e z := by
  constructor
  · intro h
    cases hr : eval exactBackend (.point x) (.point y) e with
    | none => simp [hr] at h
    | some R => exact eval_defined exactBackend_sound ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩ hr
  · rintro ⟨z, hz⟩
    obtain ⟨r, _, hr⟩ := eval_point_complete hz
    simp [hr]

/-- Automatic pointwise domain inference for exact rational coordinate functions.
The existing recursive evaluator is reused without modifying its unknown result
for general interval inputs. External uncertainty and holes are retained. -/
def inferPointDomain (x y : ℚ → ℚ) (D : DomainBounds ℚ) (e : Expr) : DomainBounds ℚ :=
  ⟨fun q => D.definite q ∧ (eval exactBackend (.point (x q)) (.point (y q)) e).isSome = true,
   fun q => D.possible q ∧ (eval exactBackend (.point (x q)) (.point (y q)) e).isSome = true,
   fun q h => ⟨D.consistent q h.1, h.2⟩⟩

instance inferPointDomain_def_dec (x y : ℚ → ℚ) (D : DomainBounds ℚ) (e : Expr) (q : ℚ)
    [Decidable (D.definite q)] : Decidable ((inferPointDomain x y D e).definite q) :=
  inferInstanceAs (Decidable (D.definite q ∧
    (eval exactBackend (.point (x q)) (.point (y q)) e).isSome = true))
instance inferPointDomain_poss_dec (x y : ℚ → ℚ) (D : DomainBounds ℚ) (e : Expr) (q : ℚ)
    [Decidable (D.possible q)] : Decidable ((inferPointDomain x y D e).possible q) :=
  inferInstanceAs (Decidable (D.possible q ∧
    (eval exactBackend (.point (x q)) (.point (y q)) e).isSome = true))

theorem inferPointDomain_possible {x y : ℚ → ℚ} {D : DomainBounds ℚ} {E : ℚ → Prop}
    (hp : ∀ q, E q → D.possible q) (e : Expr) (q : ℚ) (z : ℝ)
    (hz : E q ∧ Value (x q:ℝ) (y q:ℝ) e z) :
    (inferPointDomain x y D e).possible q :=
  ⟨hp q hz.1, (eval_point_defined_iff (x q) (y q) e).mpr ⟨z, hz.2⟩⟩

theorem inferPointDomain_definite {x y : ℚ → ℚ} {D : DomainBounds ℚ} {E : ℚ → Prop}
    (hd : ∀ q, D.definite q → E q) (e : Expr) (q : ℚ)
    (hq : (inferPointDomain x y D e).definite q) :
    ∃ z, E q ∧ Value (x q:ℝ) (y q:ℝ) e z := by
  obtain ⟨z, hz⟩ := (eval_point_defined_iff (x q) (y q) e).mp hq.2
  exact ⟨z, hd q hq.1, hz⟩

end GeneralizedIntervalArithmetic
