import LinearModelInference

namespace GeneralizedIntervalArithmetic.ReluNetworkInference

/-- Mathematical ReLU; no hardware comparison implementation is assumed. -/
def relu (z : ℝ) : ℝ := max 0 z

theorem relu_monotone : Monotone relu := fun _ _ h => max_le_max_left 0 h

def reluBounds (I : QInterval) : QInterval :=
  ⟨max 0 I.lo, max 0 I.hi, max_le_max_left 0 I.ordered⟩

theorem relu_sound {I : QInterval} {z : ℝ} (hz : I.Contains z) :
    (reluBounds I).Contains (relu z) := by
  constructor
  · simpa [reluBounds,relu] using relu_monotone hz.1
  · simpa [reluBounds,relu] using relu_monotone hz.2

/-- Every hidden neuron uses the very same input vector x. -/
def activations {n h : ℕ} (W : Fin h → Fin n → ℚ) (b : Fin h → ℚ)
    (x : Fin n → ℝ) : Fin h → ℝ :=
  fun j => relu (LinearModelInference.predict (fun i => (W j i : ℝ)) (b j) x)

def hiddenBounds {n h : ℕ} (W : Fin h → Fin n → ℚ) (b : Fin h → ℚ)
    (I : Fin n → QInterval) : Fin h → QInterval :=
  fun j => reluBounds (LinearModelInference.bounds (W j) (b j) I)

theorem hidden_sound {n h : ℕ} (W : Fin h → Fin n → ℚ) (b : Fin h → ℚ)
    {I : Fin n → QInterval} {x : Fin n → ℝ} (hx : IntervalDotProduct.InBox I x) :
    IntervalDotProduct.InBox (hiddenBounds W b I) (activations W b x) :=
  fun j => relu_sound (LinearModelInference.sound (W j) (b j) hx)

/-- Fixed rational parameters, one ReLU hidden layer, scalar affine output. -/
def predict {n h : ℕ} (W : Fin h → Fin n → ℚ) (b : Fin h → ℚ)
    (v : Fin h → ℚ) (c : ℚ) (x : Fin n → ℝ) : ℝ :=
  LinearModelInference.predict (fun j => (v j : ℝ)) c (activations W b x)

def bounds {n h : ℕ} (W : Fin h → Fin n → ℚ) (b : Fin h → ℚ)
    (v : Fin h → ℚ) (c : ℚ) (I : Fin n → QInterval) : QInterval :=
  LinearModelInference.bounds v c (hiddenBounds W b I)

/-- Marginal hidden bounds suffice for soundness, not output endpoint attainment. -/
theorem sound {n h : ℕ} (W : Fin h → Fin n → ℚ) (b : Fin h → ℚ)
    (v : Fin h → ℚ) (c : ℚ) {I : Fin n → QInterval} {x : Fin n → ℝ}
    (hx : IntervalDotProduct.InBox I x) : (bounds W b v c I).Contains (predict W b v c x) :=
  LinearModelInference.sound v c (hidden_sound W b hx)

/-- A sufficient joint-reachability condition for tightness. Individual neuron
endpoint attainment is insufficient; the whole hidden vector must be reachable. -/
theorem extrema_of_joint_reachability {n h : ℕ}
    (W : Fin h → Fin n → ℚ) (b : Fin h → ℚ) (v : Fin h → ℚ) (c : ℚ)
    (I : Fin n → QInterval)
    (reach : ∀ y, IntervalDotProduct.InBox (hiddenBounds W b I) y →
      ∃ x, IntervalDotProduct.InBox I x ∧ activations W b x = y) :
    (∃ x, IntervalDotProduct.InBox I x ∧ predict W b v c x = ((bounds W b v c I).lo : ℝ)) ∧
    (∃ x, IntervalDotProduct.InBox I x ∧ predict W b v c x = ((bounds W b v c I).hi : ℝ)) := by
  obtain ⟨⟨yl,hl,el⟩,⟨yu,hu,eu⟩⟩ := LinearModelInference.extrema v c (hiddenBounds W b I)
  obtain ⟨xl,hxl,exl⟩ := reach yl hl
  obtain ⟨xu,hxu,exu⟩ := reach yu hu
  exact ⟨⟨xl,hxl,by simpa [predict,exl] using el⟩,
    ⟨xu,hxu,by simpa [predict,exu] using eu⟩⟩

end GeneralizedIntervalArithmetic.ReluNetworkInference
