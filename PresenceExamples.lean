import ExpressionContinuity

namespace GeneralizedIntervalArithmetic

deriving instance DecidableEq for QInterval

namespace PresenceExamples

def X : QInterval := ⟨1, 2, by norm_num⟩
def Y : QInterval := .point 0
def quadratic : Expr := .sub (.mul .x .x) (.const 2)
def rationalCurve : Expr := .div quadratic (.add .x (.const 1))
def quadraticRange : QInterval := ⟨-1, 2, by norm_num⟩
def rationalRange : QInterval := ⟨-1/2, 1, by norm_num⟩

theorem quadratic_eval : eval exactBackend X Y quadratic = some quadraticRange := by
  decide +kernel

theorem quadratic_left :
    eval exactBackend (.point 1) (.point 0) quadratic = some (.point (-1)) := by
  decide +kernel

theorem quadratic_right :
    eval exactBackend (.point 2) (.point 0) quadratic = some (.point 2) := by
  decide +kernel

theorem quadratic_present :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y quadratic 0 := by
  apply evaluator_segment_presence exactBackend_sound (ax := 1) (ay := 0)
    (bx := 2) (by_ := 0) (R := quadraticRange) (L := .point (-1)) (U := .point 2)
  · norm_num [X, QInterval.Contains]
  · norm_num [Y, QInterval.Contains, QInterval.point]
  · norm_num [X, QInterval.Contains]
  · norm_num [Y, QInterval.Contains, QInterval.point]
  · exact quadratic_eval
  · exact quadratic_left
  · exact quadratic_right
  · norm_num [QInterval.point]
  · norm_num [QInterval.point]

theorem rational_eval : eval exactBackend X Y rationalCurve = some rationalRange := by
  decide +kernel

theorem rational_left :
    eval exactBackend (.point 1) (.point 0) rationalCurve = some (.point (-1/2)) := by
  decide +kernel

theorem rational_right :
    eval exactBackend (.point 2) (.point 0) rationalCurve = some (.point (2/3)) := by
  decide +kernel

theorem rational_present :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y rationalCurve 0 := by
  apply evaluator_segment_presence exactBackend_sound (ax := 1) (ay := 0)
    (bx := 2) (by_ := 0) (R := rationalRange) (L := .point (-1/2)) (U := .point (2/3))
  · norm_num [X, QInterval.Contains]
  · norm_num [Y, QInterval.Contains, QInterval.point]
  · norm_num [X, QInterval.Contains]
  · norm_num [Y, QInterval.Contains, QInterval.point]
  · exact rational_eval
  · exact rational_left
  · exact rational_right
  · norm_num [QInterval.point]
  · norm_num [QInterval.point]

def crossing : QInterval := ⟨-1, 1, by norm_num⟩
def pole : Expr := .div (.const 1) .x

/-- The two endpoint values have opposite signs, but the whole-box guard fails. -/
theorem pole_endpoint_signs :
    eval exactBackend (.point (-1)) Y pole = some (.point (-1)) ∧
    eval exactBackend (.point 1) Y pole = some (.point 1) := by decide +kernel

theorem pole_guard_rejects : eval exactBackend crossing Y pole = none := by decide +kernel

private theorem pole_value_nonzero {x y z : ℝ} (hv : Value x y pole z) : x ≠ 0 := by
  cases hv with
  | div ha hb hn => cases hb; exact hn

/-- No defined point is a root: a naive sign-change test would be unsound. -/
theorem pole_has_no_root (x y : ℝ) : ¬ Value x y pole 0 := by
  intro hv
  have he := value_eq_realValue hv
  have hn := pole_value_nonzero hv
  exact one_div_ne_zero hn (by simpa [pole, Expr.realValue] using he.symm)

end PresenceExamples
end GeneralizedIntervalArithmetic
