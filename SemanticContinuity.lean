import ExpressionContinuity
import ParameterRestriction

namespace GeneralizedIntervalArithmetic

/-- For this arithmetic-only language, definedness on a set and continuous
coordinates suffice for relative continuity. No interval interpretation is assumed. -/
theorem expr_continuousOn_of_defined {x y : ℝ → ℝ} {T : Set ℝ}
    (cx : ContinuousOn x T) (cy : ContinuousOn y T) (e : Expr)
    (hd : ∀ t ∈ T, ∃ z, Value (x t) (y t) e z) :
    ContinuousOn (fun t => e.realValue (x t) (y t)) T := by
  induction e with
  | const q => exact continuousOn_const
  | x => exact cx
  | y => exact cy
  | add a b iha ihb =>
    apply ContinuousOn.add
    · apply iha
      intro t ht
      obtain ⟨z,hz⟩ := hd t ht
      cases hz with | add ha hb => exact ⟨_,ha⟩
    · apply ihb
      intro t ht
      obtain ⟨z,hz⟩ := hd t ht
      cases hz with | add ha hb => exact ⟨_,hb⟩
  | sub a b iha ihb =>
    apply ContinuousOn.sub
    · apply iha
      intro t ht
      obtain ⟨z,hz⟩ := hd t ht
      cases hz with | sub ha hb => exact ⟨_,ha⟩
    · apply ihb
      intro t ht
      obtain ⟨z,hz⟩ := hd t ht
      cases hz with | sub ha hb => exact ⟨_,hb⟩
  | mul a b iha ihb =>
    apply ContinuousOn.mul
    · apply iha
      intro t ht
      obtain ⟨z,hz⟩ := hd t ht
      cases hz with | mul ha hb => exact ⟨_,ha⟩
    · apply ihb
      intro t ht
      obtain ⟨z,hz⟩ := hd t ht
      cases hz with | mul ha hb => exact ⟨_,hb⟩
  | div a b iha ihb =>
    apply ContinuousOn.div
    · apply iha
      intro t ht
      obtain ⟨z,hz⟩ := hd t ht
      cases hz with | div ha hb hn => exact ⟨_,ha⟩
    · apply ihb
      intro t ht
      obtain ⟨z,hz⟩ := hd t ht
      cases hz with | div ha hb hn => exact ⟨_,hb⟩
    · intro t ht
      obtain ⟨z,hz⟩ := hd t ht
      cases hz with
      | div ha hb hn => simpa [value_eq_realValue hb] using hn

/-- A canonical real expression value is accepted only with a semantic witness. -/
theorem realValue_defined {x y : ℝ} {e : Expr} (hd : ∃ z, Value x y e z) :
    Value x y e (e.realValue x y) := by
  obtain ⟨z,hz⟩ := hd
  exact value_eq_realValue hz ▸ hz

/-- The generalized guarded interpreter supplies local definedness; continuity
still requires continuous coordinate functions, not merely enclosing bounds. -/
theorem evalGuarded_continuousOn {X Y R : LinearInterval} {x y : ℝ → ℝ}
    {T : Set ℝ} {e : Expr} (ht : T ⊆ Set.Icc (0:ℝ) 1)
    (cx : ContinuousOn x T) (cy : ContinuousOn y T)
    (hx : ∀ t ∈ T, X.Contains t (x t)) (hy : ∀ t ∈ T, Y.Contains t (y t))
    (hr : evalGuarded X Y e = some R) :
    ContinuousOn (fun t => e.realValue (x t) (y t)) T ∧
      ∀ t ∈ T, Value (x t) (y t) e (e.realValue (x t) (y t)) := by
  have hd : ∀ t ∈ T, ∃ z, Value (x t) (y t) e z :=
    fun t h => evalGuarded_defined (ht h) (hx t h) (hy t h) hr
  exact ⟨expr_continuousOn_of_defined cx cy e hd,fun t h => realValue_defined (hd t h)⟩

theorem parameter_map_continuous (C : ParameterCell) : Continuous C.map :=
  segment_continuous _ _

/-- Continuity on one certified closed cell, using enclosure hypotheses only
on that original cell. This does not glue different cells across a boundary. -/
theorem evalGuarded_reparam_continuous {X Y R : LinearInterval} {x y : ℝ → ℝ}
    {e : Expr} (C : ParameterCell)
    (cx : ContinuousOn x (Set.Icc (C.interval.lo:ℝ) C.interval.hi))
    (cy : ContinuousOn y (Set.Icc (C.interval.lo:ℝ) C.interval.hi))
    (hx : ∀ t, C.interval.Contains t → X.Contains t (x t))
    (hy : ∀ t, C.interval.Contains t → Y.Contains t (y t))
    (hr : evalGuarded (X.reparam C) (Y.reparam C) e = some R) :
    ContinuousOn (fun s => e.realValue (x (C.map s)) (y (C.map s))) (Set.Icc (0:ℝ) 1) ∧
      ∀ s ∈ Set.Icc (0:ℝ) 1,
        Value (x (C.map s)) (y (C.map s)) e (e.realValue (x (C.map s)) (y (C.map s))) := by
  apply evalGuarded_continuousOn (fun _ h => h)
    (cx.comp (parameter_map_continuous C).continuousOn (fun _ h => parameter_map_mem C h))
    (cy.comp (parameter_map_continuous C).continuousOn (fun _ h => parameter_map_mem C h))
  · intro s hs
    exact (linear_reparam_contains X C s _).mpr (hx _ (parameter_map_mem C hs))
  · intro s hs
    exact (linear_reparam_contains Y C s _).mpr (hy _ (parameter_map_mem C hs))
  · exact hr

end GeneralizedIntervalArithmetic
