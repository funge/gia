import LinearEvaluator

namespace GeneralizedIntervalArithmetic

/-- Evaluation in a partial coordinate environment. Both coordinate bindings
must exist; no minimal free-variable/domain analysis is claimed. A coordinate
pair is chosen once, so repeated variable occurrences share its values. -/
def ExpressionValues (A B : ℝ → ℝ → Prop) (e : Expr) (t z : ℝ) : Prop :=
  ∃ x y, A t x ∧ B t y ∧ Value x y e z

/-- Coordinate relations need enclosure only for their actual values. Outside
their possible domains there are no values and no global enclosure obligation. -/
theorem evalLinear_relational_sound {X Y R : LinearInterval} {D E : DomainBounds ℝ}
    {A B : ℝ → ℝ → Prop} {e : Expr}
    (hX : (X.onDomain D).Sound A) (hY : (Y.onDomain E).Sound B)
    (hr : evalLinear X Y e = some R) :
    (R.onDomain (D.inter E)).Sound (ExpressionValues A B e) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro t z ⟨x, y, hx, hy, hv⟩
    exact evalLinear_sound (hX.2.1 t x hx).1 (hX.1 t x hx) (hY.1 t y hy) hv hr
  · rintro t z ⟨x, y, hx, hy, _⟩
    exact ⟨(hX.2.1 t x hx).1, (hX.2.1 t x hx).2, (hY.2.1 t y hy).2⟩
  · intro t ht
    obtain ⟨x, hx⟩ := hX.2.2 t ⟨ht.1, ht.2.1⟩
    obtain ⟨y, hy⟩ := hY.2.2 t ⟨ht.1, ht.2.2⟩
    obtain ⟨z, hz⟩ := evalLinear_defined hr x y
    exact ⟨z, x, y, hx, hy, hz⟩

/-- Function-style bridge with genuinely local hypotheses. Values of the total
representatives outside D are unrestricted and do not enter the semantics. -/
theorem evalLinear_local_sound {X Y R : LinearInterval} {e : Expr}
    {x y : ℝ → ℝ} (D : ℝ → Prop)
    (hx : ∀ t ∈ Set.Icc (0:ℝ) 1, D t → X.Contains t (x t))
    (hy : ∀ t ∈ Set.Icc (0:ℝ) 1, D t → Y.Contains t (y t))
    (hr : evalLinear X Y e = some R) :
    (R.partial.restrict D).Sound
      (fun t z => D t ∧ t ∈ Set.Icc (0:ℝ) 1 ∧ Value (x t) (y t) e z) := by
  refine ⟨?_, fun _ _ h => ⟨h.1,h.2.1⟩, ?_⟩
  · rintro t z ⟨hD, ht, hz⟩
    exact evalLinear_sound ht (hx t ht hD) (hy t ht hD) hz hr
  · intro t ht
    obtain ⟨z,hz⟩ := evalLinear_defined hr (x t) (y t)
    exact ⟨z, ht.1, ht.2, hz⟩

end GeneralizedIntervalArithmetic
