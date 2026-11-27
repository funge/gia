import LinearModelInference
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace GeneralizedIntervalArithmetic.LogisticModelInference

/-- Exact real specification, not an executable exponential implementation. -/
noncomputable def sigmoid (z : ℝ) : ℝ := Real.exp z / (1 + Real.exp z)

theorem sigmoid_strictMono : StrictMono sigmoid := by
  intro x y h
  have hx := Real.exp_pos x
  have hy := Real.exp_pos y
  have hxy := Real.exp_strictMono h
  unfold sigmoid
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem sigmoid_zero : sigmoid 0 = 1/2 := by norm_num [sigmoid]

theorem sigmoid_range (z : ℝ) : 0 < sigmoid z ∧ sigmoid z < 1 := by
  have h := Real.exp_pos z
  constructor
  · exact div_pos h (by positivity)
  · exact (div_lt_one (by positivity)).2 (by linarith)

theorem half_lt_iff (z : ℝ) : (1/2:ℝ) < sigmoid z ↔ 0 < z := by
  rw [← sigmoid_zero]
  exact sigmoid_strictMono.lt_iff_lt

theorem half_le_iff (z : ℝ) : (1/2:ℝ) ≤ sigmoid z ↔ 0 ≤ z := by
  rw [← sigmoid_zero]
  exact sigmoid_strictMono.le_iff_le

theorem lt_half_iff (z : ℝ) : sigmoid z < (1/2:ℝ) ↔ z < 0 := by
  rw [← sigmoid_zero]
  exact sigmoid_strictMono.lt_iff_lt

theorem le_half_iff (z : ℝ) : sigmoid z ≤ (1/2:ℝ) ↔ z ≤ 0 := by
  rw [← sigmoid_zero]
  exact sigmoid_strictMono.le_iff_le

/-- Any real logit threshold transports exactly, without evaluating sigmoid. -/
theorem threshold_iff (z t : ℝ) : sigmoid t < sigmoid z ↔ t < z :=
  sigmoid_strictMono.lt_iff_lt

/-- Inverse threshold for an interior probability; endpoints are excluded. -/
theorem sigmoid_log_odds {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    sigmoid (Real.log (p / (1-p))) = p := by
  have hd : 0 < 1-p := by linarith
  have hp : 0 < p / (1-p) := div_pos h0 hd
  rw [sigmoid, Real.exp_log hp]
  apply (div_eq_iff (by positivity : (1:ℝ) + p/(1-p) ≠ 0)).2
  field_simp

theorem probability_threshold_iff {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (z : ℝ) :
    p < sigmoid z ↔ Real.log (p/(1-p)) < z := by
  conv_lhs => lhs; rw [← sigmoid_log_odds h0 h1]
  exact sigmoid_strictMono.lt_iff_lt

noncomputable def predict {n : ℕ} (w : Fin n → ℝ) (b : ℝ) (x : Fin n → ℝ) : ℝ :=
  sigmoid (LinearModelInference.predict w b x)

noncomputable def lower {n : ℕ} (w : Fin n → ℚ) (b : ℚ) (I : Fin n → QInterval) : ℝ :=
  sigmoid (LinearModelInference.bounds w b I).lo
noncomputable def upper {n : ℕ} (w : Fin n → ℚ) (b : ℚ) (I : Fin n → QInterval) : ℝ :=
  sigmoid (LinearModelInference.bounds w b I).hi

theorem sound {n : ℕ} (w : Fin n → ℚ) (b : ℚ) {I : Fin n → QInterval}
    {x : Fin n → ℝ} (hx : IntervalDotProduct.InBox I x) :
    lower w b I ≤ predict (fun i => (w i : ℝ)) b x ∧
    predict (fun i => (w i : ℝ)) b x ≤ upper w b I := by
  have h := LinearModelInference.sound w b hx
  exact ⟨sigmoid_strictMono.monotone h.1, sigmoid_strictMono.monotone h.2⟩

theorem extrema {n : ℕ} (w : Fin n → ℚ) (b : ℚ) (I : Fin n → QInterval) :
    (∃ x, IntervalDotProduct.InBox I x ∧ predict (fun i => (w i : ℝ)) b x = lower w b I) ∧
    (∃ x, IntervalDotProduct.InBox I x ∧ predict (fun i => (w i : ℝ)) b x = upper w b I) := by
  obtain ⟨⟨x,hx,hl⟩,⟨y,hy,hu⟩⟩ := LinearModelInference.extrema w b I
  exact ⟨⟨x,hx,congrArg sigmoid hl⟩,⟨y,hy,congrArg sigmoid hu⟩⟩

theorem least {n : ℕ} (w : Fin n → ℚ) (b : ℚ) (I : Fin n → QInterval)
    {l u : ℝ} (h : ∀ x, IntervalDotProduct.InBox I x →
      l ≤ predict (fun i => (w i : ℝ)) b x ∧ predict (fun i => (w i : ℝ)) b x ≤ u) :
    l ≤ lower w b I ∧ upper w b I ≤ u := by
  obtain ⟨⟨x,hx,hl⟩,⟨y,hy,hu⟩⟩ := extrema w b I
  exact ⟨hl ▸ (h x hx).1, hu ▸ (h y hy).2⟩

open HardwareAddition HardwareIntervalOps

/-- A successful directed logit bound transports to real sigmoid bounds.
No executable sigmoid or tightness of rounded bounds is asserted. -/
theorem run_encloses {F : Type} {decode : F → Option ℝ}
    {add mul : Bounds F → Bounds F → Option (Bounds F)}
    (ha : OpSound decode add (· + ·)) (hm : OpSound decode mul (· * ·))
    {zero : F} (hz : decode zero = some 0)
    {n : ℕ} {W X : Fin n → Bounds F} {w x : Fin n → ℝ} {B O : Bounds F} {b l u : ℝ}
    (hw : ∀ i, Contains decode (W i) (w i))
    (hx : ∀ i, Contains decode (X i) (x i)) (hb : Contains decode B b)
    (hr : LinearModelInference.run add mul zero W X B = some O)
    (hl : decode O.lo = some l) (hu : decode O.hi = some u) :
    sigmoid l ≤ predict w b x ∧ predict w b x ≤ sigmoid u := by
  obtain ⟨l',u',hl',hu',hlo,hhi⟩ := LinearModelInference.run_encloses ha hm hz hw hx hb hr
  have el : l' = l := Option.some.inj (hl'.symm.trans hl)
  have eu : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst l'; subst u'
  exact ⟨sigmoid_strictMono.monotone hlo, sigmoid_strictMono.monotone hhi⟩

/-- Executable rational-logit threshold certificate. `none` is inconclusive.
Strict positive/negative classification deliberately leaves zero unresolved. -/
def classify (O : QInterval) : Option Bool :=
  if 0 < O.lo then some true else if O.hi < 0 then some false else none

theorem classify_true {O : QInterval} {z : ℝ} (hz : O.Contains z)
    (h : classify O = some true) : (1/2:ℝ) < sigmoid z := by
  unfold classify at h
  split_ifs at h with hl hu
  · apply (half_lt_iff z).2
    exact lt_of_lt_of_le (by exact_mod_cast hl) hz.1
  · contradiction

theorem classify_false {O : QInterval} {z : ℝ} (hz : O.Contains z)
    (h : classify O = some false) : sigmoid z < (1/2:ℝ) := by
  unfold classify at h
  split_ifs at h with hl hu
  · contradiction
  · apply (lt_half_iff z).2
    exact lt_of_le_of_lt hz.2 (by exact_mod_cast hu)

end GeneralizedIntervalArithmetic.LogisticModelInference
