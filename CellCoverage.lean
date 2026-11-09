import CellCertification

namespace GeneralizedIntervalArithmetic

/-- Conservative ordered-chain check. Nested cells do not move the frontier back.
Failure means unknown: an unsorted valid cover may fail this check. -/
def cellsCoverFrom (q : ℚ) : List ParameterCell → Bool
  | [] => false
  | C :: cells =>
    if C.interval.lo ≤ q then
      if 1 ≤ C.interval.hi then true
      else cellsCoverFrom (max q C.interval.hi) cells
    else false

private theorem cellsCoverFrom_sound {cells : List ParameterCell} {q : ℚ}
    (h : cellsCoverFrom q cells = true) {t : ℝ} (hq : (q:ℝ) ≤ t) (ht : t ≤ 1) :
    ∃ C ∈ cells, C.interval.Contains t := by
  induction cells generalizing q with
  | nil => simp [cellsCoverFrom] at h
  | cons C cells ih =>
    simp only [cellsCoverFrom] at h
    split at h
    · rename_i hlo
      have hlo' : (C.interval.lo:ℝ) ≤ t := (by exact_mod_cast hlo :
        (C.interval.lo:ℝ) ≤ q).trans hq
      split at h
      · rename_i hhi
        exact ⟨C,by simp, hlo', ht.trans (by exact_mod_cast hhi)⟩
      · by_cases hle : t ≤ (C.interval.hi:ℝ)
        · exact ⟨C,by simp,hlo',hle⟩
        · have hm : ((max q C.interval.hi:ℚ):ℝ) ≤ t := by
            rw [Rat.cast_max]
            exact max_le hq (le_of_lt (lt_of_not_ge hle))
          obtain ⟨D,hd,ht⟩ := ih h hm
          exact ⟨D,List.mem_cons_of_mem _ hd,ht⟩
    · simp at h

/-- Successful checking supplies the existing mathematical coverage predicate. -/
theorem checked_cells_cover {cells : List ParameterCell}
    (h : cellsCoverFrom 0 cells = true) : ParameterCover cells := by
  intro t ht
  exact cellsCoverFrom_sound h (by simpa using ht.1) ht.2

/-- Validate geometry first, then reuse the existing fuelled arithmetic checks.
The counter still measures evaluator attempts only, not coverage comparisons. -/
def certifyCoveredCells (X Y : LinearInterval) (e : Expr) (fuel : ℕ)
    (cells : List ParameterCell) : CellReport :=
  if cellsCoverFrom 0 cells then checkCells X Y e fuel cells else ⟨.unknown,0⟩

theorem certifyCoveredCells_call_bound (X Y : LinearInterval) (e : Expr) (fuel : ℕ)
    (cells : List ParameterCell) : (certifyCoveredCells X Y e fuel cells).checked ≤ fuel := by
  unfold certifyCoveredCells
  split
  · exact checkCells_call_bound X Y e fuel cells
  · exact Nat.zero_le fuel

theorem certifyCoveredCells_success {X Y : LinearInterval} {e : Expr} {fuel : ℕ}
    {cells : List ParameterCell}
    (h : (certifyCoveredCells X Y e fuel cells).verdict = .certified) :
    ParameterCover cells ∧ (checkCells X Y e fuel cells).verdict = .certified := by
  unfold certifyCoveredCells at h
  split at h
  · rename_i hc
    exact ⟨checked_cells_cover hc,h⟩
  · cases h

theorem certified_cells_defined {X Y : LinearInterval} {e : Expr} {fuel : ℕ}
    {cells : List ParameterCell}
    (h : (certifyCoveredCells X Y e fuel cells).verdict = .certified)
    {t x y : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y) :
    ∃ z, Value x y e z := by
  obtain ⟨hc,he⟩ := certifyCoveredCells_success h
  exact checked_cover_defined hc he ht hx hy

theorem certified_cells_continuous {X Y : LinearInterval} {e : Expr} {fuel : ℕ}
    {cells : List ParameterCell} {x y : ℝ → ℝ}
    (h : (certifyCoveredCells X Y e fuel cells).verdict = .certified)
    (cx : ContinuousOn x (Set.Icc (0:ℝ) 1)) (cy : ContinuousOn y (Set.Icc (0:ℝ) 1))
    (hx : ∀ t ∈ Set.Icc (0:ℝ) 1, X.Contains t (x t))
    (hy : ∀ t ∈ Set.Icc (0:ℝ) 1, Y.Contains t (y t)) :
    ContinuousOn (fun t => e.realValue (x t) (y t)) (Set.Icc (0:ℝ) 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, Value (x t) (y t) e (e.realValue (x t) (y t)) := by
  obtain ⟨hc,he⟩ := certifyCoveredCells_success h
  exact checked_cover_continuous hc he cx cy hx hy

end GeneralizedIntervalArithmetic
