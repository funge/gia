import ConditionalCovers
import ExpressionContinuity

namespace GeneralizedIntervalArithmetic

/-- Self-division cancels only with an actual, nonzero operand value. -/
theorem value_self_div_iff {x y u z : ℝ} {e : Expr}
    (hu : Value x y e u) (hn : u ≠ 0) : Value x y (.div e e) z ↔ z = 1 := by
  constructor
  · intro h
    cases h with
    | div ha hb _ =>
      have he := (value_eq_realValue ha).trans (value_eq_realValue hu).symm
      have hf := (value_eq_realValue hb).trans (value_eq_realValue hu).symm
      subst_vars
      exact div_self hn
  · rintro rfl
    have hv := Value.div hu hu hn
    rw [div_self hn] at hv
    exact hv

/-- A targeted proof-directed rewrite. The actual strict guard supplies the
nonzero premise only in the true branch. Retaining the guard and false branch
preserves undefinedness and equality behavior exactly. -/
theorem conditional_threshold_self_div_iff (g : Expr) (q : ℚ) (b : ConditionalExpr)
    (x y z : ℝ) :
    ConditionalValue x y (.iteLt g q
      (.leaf (.div (.sub g (.const q)) (.sub g (.const q)))) b) z ↔
    ConditionalValue x y (.iteLt g q (.leaf (.const 1)) b) z := by
  constructor
  · intro h
    cases h with
    | yes hg hlt ha =>
      have hd := Value.sub hg (Value.const q)
      have hn := sub_ne_zero.mpr (ne_of_lt hlt)
      have hz := (value_self_div_iff hd hn).mp (conditional_leaf_iff.mp ha)
      subst z
      apply ConditionalValue.yes hg hlt
      apply ConditionalValue.leaf
      simpa using (Value.const (x := x) (y := y) (1:ℚ))
    | no hg hle hb => exact ConditionalValue.no hg hle hb
  · intro h
    cases h with
    | yes hg hlt ha =>
      have hz := value_eq_realValue (conditional_leaf_iff.mp ha)
      have hz1 : z = 1 := by simpa [Expr.realValue] using hz
      apply ConditionalValue.yes hg hlt
      apply ConditionalValue.leaf
      exact (value_self_div_iff (Value.sub hg (Value.const q))
        (sub_ne_zero.mpr (ne_of_lt hlt))).mpr hz1
    | no hg hle hb => exact ConditionalValue.no hg hle hb

/-- Evaluate the rewritten expression with the existing interpreter, then
transport all three domain/enclosure obligations back through exact semantics.
This does not infer equivalence or alter interpreter failure behavior. -/
theorem evalConditionalCover_equivalent_sound {X Y : LinearInterval} {C : FiniteLinearCover}
    {D E : DomainBounds ℝ} {A B : ℝ → ℝ → Prop} {original rewritten : ConditionalExpr}
    (he : ∀ x y z, ConditionalValue x y original z ↔ ConditionalValue x y rewritten z)
    (hX : (X.onDomain D).Sound A) (hY : (Y.onDomain E).Sound B)
    (hr : evalConditionalCover X Y rewritten = some C) :
    C.SoundOn (D.inter E) (ConditionalExpressionValues A B original) := by
  have hc := evalConditionalCover_relational_sound hX hY hr
  refine ⟨?_,?_,?_⟩
  · rintro t z ⟨x,y,hx,hy,hv⟩
    exact hc.1 t z ⟨x,y,hx,hy,(he x y z).mp hv⟩
  · rintro t z ⟨x,y,hx,hy,hv⟩
    exact hc.2.1 t z ⟨x,y,hx,hy,(he x y z).mp hv⟩
  · intro t ht
    obtain ⟨z,x,y,hx,hy,hv⟩ := hc.2.2 t ht
    exact ⟨z,x,y,hx,hy,(he x y z).mpr hv⟩

end GeneralizedIntervalArithmetic
