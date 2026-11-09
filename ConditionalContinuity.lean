import CellContinuity
import ConditionalEvaluator

namespace GeneralizedIntervalArithmetic

/-- A semantic representative, not another expression language. Equality takes
 the false branch, consistently with ConditionalValue. -/
noncomputable def thresholdValue (q : ℚ) (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t < (q:ℝ) then f t else g t

private theorem threshold_left {q : ℚ} {f g : ℝ → ℝ}
    (hm : f q = g q) {t : ℝ} (ht : t ≤ (q:ℝ)) : thresholdValue q f g t = f t := by
  unfold thresholdValue
  split
  · rfl
  · rename_i hn
    have he : t = (q:ℝ) := le_antisymm ht (le_of_not_gt hn)
    subst t
    exact hm.symm

private theorem threshold_right {q : ℚ} {f g : ℝ → ℝ} {t : ℝ}
    (ht : (q:ℝ) ≤ t) : thresholdValue q f g t = g t := by
  simp [thresholdValue,not_lt_of_ge ht]

/-- A sufficient matching-boundary rule, proved through existing closed-cover
composition. This does not infer limits or equality of branch representatives. -/
theorem threshold_continuous (q : ℚ) (hq : 0 ≤ q ∧ q ≤ 1) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0:ℝ) q))
    (hg : ContinuousOn g (Set.Icc (q:ℝ) 1)) (hm : f q = g q) :
    ContinuousOn (thresholdValue q f g) (Set.Icc (0:ℝ) 1) := by
  let L : ParameterCell := ⟨⟨0,q,hq.1⟩,le_rfl,hq.2⟩
  let R : ParameterCell := ⟨⟨q,1,hq.2⟩,hq.1,le_rfl⟩
  have hc : ParameterCover [L,R] := by
    intro t ht
    by_cases h : t ≤ (q:ℝ)
    · refine ⟨L,by simp,?_⟩
      simpa [L,QInterval.Contains] using And.intro ht.1 h
    · refine ⟨R,by simp,?_⟩
      simpa [R,QInterval.Contains] using And.intro (le_of_not_ge h) ht.2
  have hl : ContinuousOn (thresholdValue q f g) (Set.Icc (0:ℝ) q) :=
    hf.congr (fun _ ht => threshold_left hm ht.2)
  have hr : ContinuousOn (thresholdValue q f g) (Set.Icc (q:ℝ) 1) :=
    hg.congr (fun _ ht => threshold_right ht.1)
  apply parameter_cover_continuous hc
  intro C hC
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
  rcases hC with rfl | rfl
  · apply (parameter_cell_continuous_iff L _).mp
    simpa [L] using hl
  · apply (parameter_cell_continuous_iff R _).mp
    simpa [R] using hr

/-- The guard's actual value is the parameter. The true branch is needed only
strictly below q; its continuous representative at q is a limit witness, not a
claim that the true branch is defined there. The false branch includes equality. -/
theorem conditional_threshold_certificate {x y f g : ℝ → ℝ}
    {guard : Expr} {a b : ConditionalExpr} (q : ℚ) (hq : 0 ≤ q ∧ q ≤ 1)
    (hguard : ∀ t ∈ Set.Icc (0:ℝ) 1, Value (x t) (y t) guard t)
    (hf : ContinuousOn f (Set.Icc (0:ℝ) q))
    (hg : ContinuousOn g (Set.Icc (q:ℝ) 1)) (hm : f q = g q)
    (ha : ∀ t, 0 ≤ t → t < (q:ℝ) → ConditionalValue (x t) (y t) a (f t))
    (hb : ∀ t ∈ Set.Icc (q:ℝ) 1, ConditionalValue (x t) (y t) b (g t)) :
    ContinuousOn (thresholdValue q f g) (Set.Icc (0:ℝ) 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1,
        ConditionalValue (x t) (y t) (.iteLt guard q a b) (thresholdValue q f g t) := by
  refine ⟨threshold_continuous q hq f g hf hg hm,?_⟩
  intro t ht
  by_cases h : t < (q:ℝ)
  · simpa [thresholdValue,h] using ConditionalValue.yes (hguard t ht) h (ha t ht.1 h)
  · simpa [thresholdValue,h] using ConditionalValue.no (hguard t ht) (le_of_not_gt h)
      (hb t ⟨le_of_not_gt h,ht.2⟩)

end GeneralizedIntervalArithmetic
