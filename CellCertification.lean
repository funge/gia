import SemanticContinuity

namespace GeneralizedIntervalArithmetic

inductive CellVerdict | certified | unknown deriving DecidableEq, Repr

/-- checked counts calls to evalGuarded, not arithmetic operations or time. -/
structure CellReport where
  verdict : CellVerdict
  checked : ℕ
  deriving DecidableEq, Repr

/-- Check a supplied list, stopping at the first failed enclosure or fuel exhaustion.
Certification of the list alone does not prove that it covers the parameter range. -/
def checkCells (X Y : LinearInterval) (e : Expr) : ℕ → List ParameterCell → CellReport
  | _, [] => ⟨.certified,0⟩
  | 0, _ :: _ => ⟨.unknown,0⟩
  | n+1, C :: cells =>
    if (evalGuarded (X.reparam C) (Y.reparam C) e).isSome then
      let r := checkCells X Y e n cells
      ⟨r.verdict,r.checked+1⟩
    else ⟨.unknown,1⟩

theorem checkCells_call_bound (X Y : LinearInterval) (e : Expr) (n : ℕ)
    (cells : List ParameterCell) : (checkCells X Y e n cells).checked ≤ n := by
  induction n generalizing cells with
  | zero => cases cells <;> simp [checkCells]
  | succ n ih =>
    cases cells with
    | nil => simp [checkCells]
    | cons C cells =>
      simp only [checkCells]
      split
      · exact Nat.succ_le_succ (ih cells)
      · exact Nat.succ_le_succ (Nat.zero_le n)

theorem checkCells_certified_count {X Y : LinearInterval} {e : Expr} {n : ℕ}
    {cells : List ParameterCell} (h : (checkCells X Y e n cells).verdict = .certified) :
    (checkCells X Y e n cells).checked = cells.length := by
  induction n generalizing cells with
  | zero => cases cells <;> simp_all [checkCells]
  | succ n ih =>
    cases cells with
    | nil => rfl
    | cons C cells =>
      simp only [checkCells] at h ⊢
      split at h
      · rename_i he
        simp only [he,if_true]
        exact congrArg Nat.succ (ih h)
      · cases h

theorem checkCells_certified_budget {X Y : LinearInterval} {e : Expr} {n : ℕ}
    {cells : List ParameterCell} (h : (checkCells X Y e n cells).verdict = .certified) :
    cells.length ≤ n := by
  rw [← checkCells_certified_count h]
  exact checkCells_call_bound X Y e n cells

theorem checkCells_successful_member {X Y : LinearInterval} {e : Expr} {n : ℕ}
    {cells : List ParameterCell} (h : (checkCells X Y e n cells).verdict = .certified)
    {C : ParameterCell} (hc : C ∈ cells) :
    ∃ I, evalGuarded (X.reparam C) (Y.reparam C) e = some I := by
  induction n generalizing cells with
  | zero => cases cells <;> simp_all [checkCells]
  | succ n ih =>
    cases cells with
    | nil => simp at hc
    | cons K cells =>
      simp only [checkCells] at h
      split at h
      · rename_i he
        rcases List.mem_cons.mp hc with rfl | hc
        · cases hg : evalGuarded (X.reparam C) (Y.reparam C) e with
          | none => simp [hg] at he
          | some I => exact ⟨I,rfl⟩
        · exact ih h hc
      · cases h

/-- A coverage proof supplies a checked cell at every point, including boundaries.
Definedness remains local to the actual enclosed coordinates. -/
theorem checked_cover_defined {X Y : LinearInterval} {e : Expr} {n : ℕ}
    {cells : List ParameterCell} (hc : ParameterCover cells)
    (h : (checkCells X Y e n cells).verdict = .certified)
    {t x y : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y) :
    ∃ z, Value x y e z := by
  obtain ⟨C,hC,s,hs,he⟩ := parameter_cover_pullback hc ht
  obtain ⟨I,hI⟩ := checkCells_successful_member h hC
  apply evalGuarded_defined hs (R := I)
  · exact (linear_reparam_contains X C s x).mpr (he.symm ▸ hx)
  · exact (linear_reparam_contains Y C s y).mpr (he.symm ▸ hy)
  · exact hI

/-- Arithmetic continuity is derived, not assumed per cell. Coordinate continuity
and a supplied full cover remain explicit. No conditional continuity is inferred. -/
theorem checked_cover_continuous {X Y : LinearInterval} {e : Expr} {n : ℕ}
    {cells : List ParameterCell} {x y : ℝ → ℝ} (hc : ParameterCover cells)
    (h : (checkCells X Y e n cells).verdict = .certified)
    (cx : ContinuousOn x (Set.Icc (0:ℝ) 1)) (cy : ContinuousOn y (Set.Icc (0:ℝ) 1))
    (hx : ∀ t ∈ Set.Icc (0:ℝ) 1, X.Contains t (x t))
    (hy : ∀ t ∈ Set.Icc (0:ℝ) 1, Y.Contains t (y t)) :
    ContinuousOn (fun t => e.realValue (x t) (y t)) (Set.Icc (0:ℝ) 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, Value (x t) (y t) e (e.realValue (x t) (y t)) := by
  have hd := fun t ht => checked_cover_defined hc h ht (hx t ht) (hy t ht)
  exact ⟨expr_continuousOn_of_defined cx cy e hd,fun t ht => realValue_defined (hd t ht)⟩

end GeneralizedIntervalArithmetic
