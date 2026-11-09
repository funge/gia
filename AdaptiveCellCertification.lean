import CellCoverage
import Subdivision

namespace GeneralizedIntervalArithmetic

def ParameterCell.unit : ParameterCell := ⟨⟨0,1,by norm_num⟩,le_rfl,le_rfl⟩
def ParameterCell.lowerHalf (C : ParameterCell) : ParameterCell :=
  ⟨C.interval.lowerHalf,C.nonneg,(midpoint_bounds C.interval).2.trans C.le_one⟩
def ParameterCell.upperHalf (C : ParameterCell) : ParameterCell :=
  ⟨C.interval.upperHalf,C.nonneg.trans (midpoint_bounds C.interval).1,C.le_one⟩

structure AdaptiveCellPlan where
  cells : List ParameterCell
  checked : ℕ

/-- Full binary-tree attempt bound: B(0)=1, B(d+1)=1+B(d)+B(d). -/
def adaptiveCallBudget : ℕ → ℕ
  | 0 => 1
  | d+1 => 1 + adaptiveCallBudget d + adaptiveCallBudget d

/-- One call to the existing single-cell checker per visited node. Unresolved
leaves are retained when depth is exhausted; they are never treated as empty. -/
def planAdaptiveCells (X Y : LinearInterval) (e : Expr) : ℕ → ParameterCell → AdaptiveCellPlan
  | depth, C =>
    if (checkCells X Y e 1 [C]).verdict = .certified then ⟨[C],1⟩
    else match depth with
      | 0 => ⟨[C],1⟩
      | d+1 =>
        let L := planAdaptiveCells X Y e d C.lowerHalf
        let R := planAdaptiveCells X Y e d C.upperHalf
        ⟨L.cells ++ R.cells,1 + L.checked + R.checked⟩

theorem single_cell_attempt_count (X Y : LinearInterval) (e : Expr) (C : ParameterCell) :
    (checkCells X Y e 1 [C]).checked = 1 := by
  simp only [checkCells]
  split <;> rfl

theorem adaptive_plan_call_bound (X Y : LinearInterval) (e : Expr) (depth : ℕ)
    (C : ParameterCell) : (planAdaptiveCells X Y e depth C).checked ≤ adaptiveCallBudget depth := by
  induction depth generalizing C with
  | zero => simp [planAdaptiveCells,adaptiveCallBudget]
  | succ d ih =>
    simp only [planAdaptiveCells]
    split
    · simp only [adaptiveCallBudget]
      omega
    · exact Nat.add_le_add (Nat.add_le_add_left (ih C.lowerHalf) 1) (ih C.upperHalf)

/-- Every point in the parent remains in a generated cell, even on exhaustion. -/
theorem adaptive_plan_covers (X Y : LinearInterval) (e : Expr) (depth : ℕ)
    (C : ParameterCell) {t : ℝ} (ht : C.interval.Contains t) :
    ∃ D ∈ (planAdaptiveCells X Y e depth C).cells, D.interval.Contains t := by
  induction depth generalizing C with
  | zero => simp [planAdaptiveCells,ht]
  | succ d ih =>
    simp only [planAdaptiveCells]
    split
    · exact ⟨C,by simp,ht⟩
    · rcases (split_cover C.interval t).mp ht with hl | hr
      · obtain ⟨D,hd,ht⟩ := ih C.lowerHalf hl
        exact ⟨D,List.mem_append_left _ hd,ht⟩
      · obtain ⟨D,hd,ht⟩ := ih C.upperHalf hr
        exact ⟨D,List.mem_append_right _ hd,ht⟩

/-- Generated cells stay within their parent; the producer only refines geometry. -/
theorem adaptive_plan_subset (X Y : LinearInterval) (e : Expr) (depth : ℕ)
    (C : ParameterCell) {D : ParameterCell}
    (hd : D ∈ (planAdaptiveCells X Y e depth C).cells) {t : ℝ}
    (ht : D.interval.Contains t) : C.interval.Contains t := by
  induction depth generalizing C with
  | zero =>
    simp [planAdaptiveCells] at hd
    subst D
    exact ht
  | succ d ih =>
    simp only [planAdaptiveCells] at hd
    split at hd
    · have he := List.mem_singleton.mp hd
      subst D
      exact ht
    · rcases List.mem_append.mp hd with hl | hr
      · exact lowerHalf_subset (ih C.lowerHalf hl)
      · exact upperHalf_subset (ih C.upperHalf hr)

theorem adaptive_unit_cover (X Y : LinearInterval) (e : Expr) (depth : ℕ) :
    ParameterCover (planAdaptiveCells X Y e depth ParameterCell.unit).cells := by
  intro t ht
  exact adaptive_plan_covers X Y e depth ParameterCell.unit
    (by simpa [ParameterCell.unit,QInterval.Contains] using ht)

/-- Retain the full binary-tree bound for planning and a separate evaluator-call
budget for validation. The reported count includes both stages, including rechecks. -/
def certifyAdaptiveCells (X Y : LinearInterval) (e : Expr) (depth fuel : ℕ) : CellReport :=
  let p := planAdaptiveCells X Y e depth ParameterCell.unit
  let r := certifyCoveredCells X Y e fuel p.cells
  ⟨r.verdict,p.checked+r.checked⟩

theorem adaptive_certificate_call_bound (X Y : LinearInterval) (e : Expr) (depth fuel : ℕ) :
    (certifyAdaptiveCells X Y e depth fuel).checked ≤ adaptiveCallBudget depth + fuel :=
  Nat.add_le_add (adaptive_plan_call_bound X Y e depth ParameterCell.unit)
    (certifyCoveredCells_call_bound X Y e fuel _)

theorem adaptive_certified_defined {X Y : LinearInterval} {e : Expr} {depth fuel : ℕ}
    (h : (certifyAdaptiveCells X Y e depth fuel).verdict = .certified)
    {t x y : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y) :
    ∃ z, Value x y e z := certified_cells_defined h ht hx hy

theorem adaptive_certified_continuous {X Y : LinearInterval} {e : Expr} {depth fuel : ℕ}
    {x y : ℝ → ℝ} (h : (certifyAdaptiveCells X Y e depth fuel).verdict = .certified)
    (cx : ContinuousOn x (Set.Icc (0:ℝ) 1)) (cy : ContinuousOn y (Set.Icc (0:ℝ) 1))
    (hx : ∀ t ∈ Set.Icc (0:ℝ) 1, X.Contains t (x t))
    (hy : ∀ t ∈ Set.Icc (0:ℝ) 1, Y.Contains t (y t)) :
    ContinuousOn (fun t => e.realValue (x t) (y t)) (Set.Icc (0:ℝ) 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, Value (x t) (y t) e (e.realValue (x t) (y t)) :=
  certified_cells_continuous h cx cy hx hy

end GeneralizedIntervalArithmetic
