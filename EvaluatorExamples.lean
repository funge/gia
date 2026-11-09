import EvaluatorRounding

namespace GeneralizedIntervalArithmetic.Examples

def X : QInterval := ⟨2, 3, by norm_num⟩
def Y : QInterval := ⟨0, 1, by norm_num⟩
def cross : QInterval := ⟨-1, 1, by norm_num⟩

/-- Exercises every arithmetic constructor: (x*x - 1)/(y + 2). -/
def mixed : Expr := .div (.sub (.mul .x .x) (.const 1)) (.add .y (.const 2))

def bounds (B : Backend) (X Y : QInterval) (e : Expr) : Option (ℚ × ℚ) :=
  (eval B X Y e).map (fun I => (I.lo, I.hi))

local macro "check_bounds" : tactic => `(tactic| decide +kernel)

theorem mixed_bounds : bounds exactBackend X Y mixed = some (1, 4) := by check_bounds

theorem mixed_empty : classifyExpr exactBackend X Y mixed = .empty := by check_bounds

theorem mixed_no_root : ¬ ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y mixed 0 :=
  eval_empty_pixel exactBackend_sound mixed_empty

theorem negative_divisor :
    bounds exactBackend ⟨3, 8, by norm_num⟩ ⟨-3, -2, by norm_num⟩ (.div .x .y) =
      some (-4, -1) := by check_bounds

theorem mixed_sign_product :
    bounds exactBackend ⟨-2, 3, by norm_num⟩ ⟨-4, 5, by norm_num⟩ (.mul .x .y) =
      some (-12, 15) := by check_bounds

theorem crossing_zero_unknown :
    eval exactBackend X cross (.div .x .y) = none := by
  apply Option.isNone_iff_eq_none.mp
  check_bounds

theorem touching_zero_unknown :
    classifyExpr exactBackend X Y (.div .x .y) = .unknown := by check_bounds

/-- The uncertain box still has defined points; none is not a domain verdict. -/
theorem unknown_with_defined_point :
    classifyExpr exactBackend cross Y (.div (.const 1) .x) = .unknown ∧
    Value 1 0 (.div (.const 1) .x) 1 := by
  constructor
  · check_bounds
  · simpa using Value.div (Value.const (x := (1 : ℝ)) (y := (0 : ℝ)) 1)
      Value.x (by norm_num : (1 : ℝ) ≠ 0)

/-- Dependency loss can make even a total expression's denominator uncertain. -/
theorem dependency_unknown :
    eval exactBackend cross Y (.div (.const 1) (.add (.mul .x .x) (.const 1))) =
      none := by
  apply Option.isNone_iff_eq_none.mp
  check_bounds

theorem dependency_defined_everywhere (x y : ℝ) :
    Value x y (.div (.const 1) (.add (.mul .x .x) (.const 1))) (1 / (x*x + 1)) := by
  have hn : x*x + (1 : ℝ) ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (mul_self_nonneg x) zero_lt_one)
  have hv : Value x y (.add (.mul .x .x) (.const 1)) (x*x + 1) := by
    simpa using Value.add (Value.mul (Value.x (x := x) (y := y)) Value.x) (Value.const 1)
  simpa using Value.div (Value.const 1) hv hn

theorem division_by_zero_undefined (x y z : ℝ) :
    ¬ Value x y (.div (.const 1) (.const 0)) z := by
  intro h
  cases h with
  | div ha hb hn => cases hb; exact hn (by norm_num)

/-- A synthetic widening backend, not an IEEE rounding algorithm. It demonstrates
that the common proof does not depend on exact endpoints or nearest rounding. -/
def coarseDown (q : ℚ) : Option ℚ := some (q - 1)
def coarseUp (q : ℚ) : Option ℚ := some (q + 1)

theorem coarseDown_contract : ∀ q r, coarseDown q = some r → r ≤ q := by
  intro q r h
  cases h
  exact sub_le_self _ (by norm_num)

theorem coarseUp_contract : ∀ q r, coarseUp q = some r → q ≤ r := by
  intro q r h
  cases h
  exact le_add_of_nonneg_right (by norm_num)

theorem coarse_backend_sound : BackendSound (directedBackend coarseDown coarseUp) :=
  directedBackend_sound _ _ coarseDown_contract coarseUp_contract

theorem widening_can_force_unknown :
    eval (directedBackend coarseDown coarseUp) X Y (.div .x (.const 1)) = none := by
  apply Option.isNone_iff_eq_none.mp
  check_bounds

theorem failed_rounding_unknown :
    eval (directedBackend (fun _ => none) some) X Y (.add .x .y) = none := by
  simp [eval, combine, directedBackend]

end GeneralizedIntervalArithmetic.Examples
