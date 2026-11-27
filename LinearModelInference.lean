import DirectedDotProduct

namespace GeneralizedIntervalArithmetic.LinearModelInference
open IntervalDotProduct

/-- Prediction with supplied fixed parameters; no fitting or training. -/
def predict {n : ℕ} (w : Fin n → ℝ) (bias : ℝ) (x : Fin n → ℝ) : ℝ :=
  dot w x + bias

def bounds {n : ℕ} (w : Fin n → ℚ) (bias : ℚ) (I : Fin n → QInterval) : QInterval :=
  (weightedBounds w I).add (QInterval.point bias)

theorem sound {n : ℕ} (w : Fin n → ℚ) (bias : ℚ) {I : Fin n → QInterval}
    {x : Fin n → ℝ} (hx : InBox I x) :
    (bounds w bias I).Contains (predict (fun i => (w i : ℝ)) bias x) :=
  add_encloses (weighted_sound w hx) ⟨le_rfl,le_rfl⟩

theorem extrema {n : ℕ} (w : Fin n → ℚ) (bias : ℚ) (I : Fin n → QInterval) :
    (∃ x, InBox I x ∧ predict (fun i => (w i : ℝ)) bias x = ((bounds w bias I).lo : ℝ)) ∧
    (∃ x, InBox I x ∧ predict (fun i => (w i : ℝ)) bias x = ((bounds w bias I).hi : ℝ)) := by
  obtain ⟨⟨x,hx,hl⟩,⟨y,hy,hu⟩⟩ := weighted_extrema w I
  constructor
  · exact ⟨x,hx,by simp [predict,bounds,QInterval.add,QInterval.point,hl]⟩
  · exact ⟨y,hy,by simp [predict,bounds,QInterval.add,QInterval.point,hu]⟩

theorem least {n : ℕ} (w : Fin n → ℚ) (bias : ℚ) (I : Fin n → QInterval)
    {l u : ℝ} (h : ∀ x, InBox I x → l ≤ predict (fun i => (w i : ℝ)) bias x ∧
      predict (fun i => (w i : ℝ)) bias x ≤ u) :
    l ≤ ((bounds w bias I).lo : ℝ) ∧ ((bounds w bias I).hi : ℝ) ≤ u := by
  obtain ⟨⟨x,hx,hl⟩,⟨y,hy,hu⟩⟩ := extrema w bias I
  exact ⟨hl ▸ (h x hx).1,hu ▸ (h y hy).2⟩

/-- A strict prediction threshold. Equality at the lower endpoint is insufficient. -/
theorem above_threshold {n : ℕ} (w : Fin n → ℚ) (bias : ℚ) {I : Fin n → QInterval}
    {threshold : ℝ} (h : threshold < ((bounds w bias I).lo : ℝ))
    {x : Fin n → ℝ} (hx : InBox I x) :
    threshold < predict (fun i => (w i : ℝ)) bias x := h.trans_le (sound w bias hx).1

open HardwareAddition HardwareIntervalOps

/-- Fixed dot-product order, then one final bias addition. Bias is not moved
into the initial accumulator; that would be a different rounded program. -/
def run {F : Type} (add mul : Bounds F → Bounds F → Option (Bounds F))
    (zero : F) {n : ℕ} (W X : Fin n → Bounds F) (B : Bounds F) : Option (Bounds F) := do
  let D ← DirectedDotProduct.run add mul zero W X
  add D B

theorem run_encloses {F : Type} {decode : F → Option ℝ}
    {add mul : Bounds F → Bounds F → Option (Bounds F)}
    (ha : OpSound decode add (· + ·)) (hm : OpSound decode mul (· * ·))
    {zero : F} (hz : decode zero = some 0)
    {n : ℕ} {W X : Fin n → Bounds F} {w x : Fin n → ℝ} {B O : Bounds F} {b : ℝ}
    (hw : ∀ i, Contains decode (W i) (w i))
    (hx : ∀ i, Contains decode (X i) (x i)) (hb : Contains decode B b)
    (hr : run add mul zero W X B = some O) : Contains decode O (predict w b x) := by
  unfold run at hr
  cases hd : DirectedDotProduct.run add mul zero W X with
  | none => simp [hd] at hr
  | some D =>
    have hadd : add D B = some O := by simpa [hd] using hr
    exact ha _ _ _ _ _ hadd (DirectedDotProduct.run_encloses ha hm hz hw hx hd) hb

theorem dot_failure {F : Type} (add mul : Bounds F → Bounds F → Option (Bounds F))
    (zero : F) {n : ℕ} (W X : Fin n → Bounds F) (B : Bounds F)
    (h : DirectedDotProduct.run add mul zero W X = none) :
    run add mul zero W X B = none := by simp [run,h]

theorem bias_failure {F : Type} (add mul : Bounds F → Bounds F → Option (Bounds F))
    (zero : F) {n : ℕ} (W X : Fin n → Bounds F) (B D : Bounds F)
    (hd : DirectedDotProduct.run add mul zero W X = some D) (h : add D B = none) :
    run add mul zero W X B = none := by simp [run,hd,h]

end GeneralizedIntervalArithmetic.LinearModelInference
