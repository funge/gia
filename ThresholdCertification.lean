import ExpressionContinuity
import ConditionalCovers
import ParameterRestriction

namespace GeneralizedIntervalArithmetic

def ParameterCell.thresholdLeft (q : ℚ) (hq : 0 ≤ q ∧ q ≤ 1) : ParameterCell :=
  ⟨⟨0,q,hq.1⟩,le_rfl,hq.2⟩
def ParameterCell.thresholdRight (q : ℚ) (hq : 0 ≤ q ∧ q ≤ 1) : ParameterCell :=
  ⟨⟨q,1,hq.2⟩,hq.1,le_rfl⟩

/-- Each result uses its own cell's unit parameter. These lists must not be
concatenated as if they shared the original global parameter. Both closed-cell
checks must succeed, including the true branch's inactive boundary point. -/
def evalThresholdBranches (X Y : LinearInterval) (q : ℚ) (hq : 0 ≤ q ∧ q ≤ 1)
    (a b : ConditionalExpr) : Option (FiniteLinearCover × FiniteLinearCover) := do
  let A ← evalConditionalCover (X.reparam (.thresholdLeft q hq))
    (Y.reparam (.thresholdLeft q hq)) a
  let B ← evalConditionalCover (X.reparam (.thresholdRight q hq))
    (Y.reparam (.thresholdRight q hq)) b
  pure (A,B)

theorem threshold_branches_success {X Y : LinearInterval} {q : ℚ} {hq : 0 ≤ q ∧ q ≤ 1}
    {a b : ConditionalExpr} {A B : FiniteLinearCover}
    (h : evalThresholdBranches X Y q hq a b = some (A,B)) :
    evalConditionalCover (X.reparam (.thresholdLeft q hq))
      (Y.reparam (.thresholdLeft q hq)) a = some A ∧
    evalConditionalCover (X.reparam (.thresholdRight q hq))
      (Y.reparam (.thresholdRight q hq)) b = some B := by
  unfold evalThresholdBranches at h
  cases ha : evalConditionalCover (X.reparam (.thresholdLeft q hq))
      (Y.reparam (.thresholdLeft q hq)) a <;>
    cases hb : evalConditionalCover (X.reparam (.thresholdRight q hq))
      (Y.reparam (.thresholdRight q hq)) b <;> simp_all

private theorem cell_defined {X Y : LinearInterval} {C : ParameterCell}
    {e : ConditionalExpr} {F : FiniteLinearCover} {t x y : ℝ}
    (ht : C.interval.Contains t) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hr : evalConditionalCover (X.reparam C) (Y.reparam C) e = some F) :
    ∃ z, ConditionalValue x y e z := by
  obtain ⟨s,hs,rfl⟩ := parameter_map_onto C ht
  exact evalConditionalCover_defined hs ((linear_reparam_contains X C s x).mpr hx)
    ((linear_reparam_contains Y C s y).mpr hy) hr

private theorem cell_encloses {X Y : LinearInterval} {C : ParameterCell}
    {e : ConditionalExpr} {F : FiniteLinearCover} {t x y z : ℝ}
    (ht : C.interval.Contains t) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hr : evalConditionalCover (X.reparam C) (Y.reparam C) e = some F)
    (hz : ConditionalValue x y e z) :
    ∃ s ∈ Set.Icc (0:ℝ) 1, C.map s = t ∧ ∃ I ∈ F, I.Contains s z := by
  obtain ⟨s,hs,he⟩ := parameter_map_onto C ht
  refine ⟨s,hs,he,?_⟩
  subst t
  exact evalConditionalCover_sound hs ((linear_reparam_contains X C s x).mpr hx)
    ((linear_reparam_contains Y C s y).mpr hy) hz hr

/-- The guard identity is a supplied actual Value proof, not inferred from the
branch checks. Equality selects the false branch. No continuity is concluded. -/
theorem threshold_branches_defined {X Y : LinearInterval} {q : ℚ} {hq : 0 ≤ q ∧ q ≤ 1}
    {a b : ConditionalExpr} {A B : FiniteLinearCover} {g : Expr} {t x y : ℝ}
    (hr : evalThresholdBranches X Y q hq a b = some (A,B))
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hg : Value x y g t) : ∃ z, ConditionalValue x y (.iteLt g q a b) z := by
  obtain ⟨ha,hb⟩ := threshold_branches_success hr
  by_cases h : t < (q:ℝ)
  · have hc : (ParameterCell.thresholdLeft q hq).interval.Contains t := by
      simpa [ParameterCell.thresholdLeft,QInterval.Contains] using And.intro ht.1 h.le
    obtain ⟨z,hz⟩ := cell_defined hc hx hy ha
    exact ⟨z,ConditionalValue.yes hg h hz⟩
  · have hc : (ParameterCell.thresholdRight q hq).interval.Contains t := by
      simpa [ParameterCell.thresholdRight,QInterval.Contains] using And.intro (le_of_not_gt h) ht.2
    obtain ⟨z,hz⟩ := cell_defined hc hx hy hb
    exact ⟨z,ConditionalValue.no hg (le_of_not_gt h) hz⟩

/-- Actual values are enclosed in the active cell's local parameter, never in
a flattened global affine range. The guard must have actual value t. -/
theorem threshold_branches_enclose {X Y : LinearInterval} {q : ℚ} {hq : 0 ≤ q ∧ q ≤ 1}
    {a b : ConditionalExpr} {A B : FiniteLinearCover} {g : Expr} {t x y z : ℝ}
    (hr : evalThresholdBranches X Y q hq a b = some (A,B))
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hg : Value x y g t) (hz : ConditionalValue x y (.iteLt g q a b) z) :
    (t < (q:ℝ) ∧ ∃ s ∈ Set.Icc (0:ℝ) 1, (ParameterCell.thresholdLeft q hq).map s = t ∧
      ∃ I ∈ A, I.Contains s z) ∨
    ((q:ℝ) ≤ t ∧ ∃ s ∈ Set.Icc (0:ℝ) 1, (ParameterCell.thresholdRight q hq).map s = t ∧
      ∃ I ∈ B, I.Contains s z) := by
  obtain ⟨ha,hb⟩ := threshold_branches_success hr
  cases hz with
  | yes hk hlt hv =>
    have he := (value_eq_realValue hk).trans (value_eq_realValue hg).symm
    subst_vars
    exact Or.inl ⟨hlt,cell_encloses (by
      simpa [ParameterCell.thresholdLeft,QInterval.Contains] using And.intro ht.1 hlt.le) hx hy ha hv⟩
  | no hk hle hv =>
    have he := (value_eq_realValue hk).trans (value_eq_realValue hg).symm
    subst_vars
    exact Or.inr ⟨hle,cell_encloses (by
      simpa [ParameterCell.thresholdRight,QInterval.Contains] using And.intro hle ht.2) hx hy hb hv⟩

theorem threshold_branches_exclude_zero {X Y : LinearInterval} {q : ℚ} {hq : 0 ≤ q ∧ q ≤ 1}
    {a b : ConditionalExpr} {A B : FiniteLinearCover} {g : Expr} {t x y : ℝ}
    (hr : evalThresholdBranches X Y q hq a b = some (A,B))
    (ha : ∀ I ∈ A, I.hull.AwayZero) (hb : ∀ I ∈ B, I.hull.AwayZero)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hg : Value x y g t) : ¬ ConditionalValue x y (.iteLt g q a b) 0 := by
  intro hz
  rcases threshold_branches_enclose hr ht hx hy hg hz with
    ⟨_,s,hs,_,I,hi,hI⟩ | ⟨_,s,hs,_,I,hi,hI⟩
  · exact awayZero_nonzero (ha I hi) (linear_hull_encloses hs hI) rfl
  · exact awayZero_nonzero (hb I hi) (linear_hull_encloses hs hI) rfl

end GeneralizedIntervalArithmetic
