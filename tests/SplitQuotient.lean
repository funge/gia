import SplitQuotient
import AuditPolicy
import Mathlib.Analysis.Convex.Basic

namespace GeneralizedIntervalArithmetic.SplitQuotientChecks
open SplitQuotient

def one (_ : Unit) (x : ℝ) := x = 1
def crossing (_ : Unit) (y : ℝ) := -2 ≤ y ∧ y ≤ 1

theorem reciprocal_exact (z : ℝ) :
    QuotientValues one crossing () z ↔ z ≤ -1/2 ∨ 1 ≤ z := by
  have h := reciprocal_image (z := z) (l := -2) (u := 1) (by norm_num) (by norm_num)
  norm_num [QuotientValues,one,crossing,and_assoc] at h ⊢
  exact h

theorem nonzero_window_excluded : ¬ ∃ z, QuotientValues one crossing () z ∧
    (1/4 : ℝ) ≤ z ∧ z ≤ 3/4 := by
  rintro ⟨z,hz,hl,hu⟩
  rcases (reciprocal_exact z).mp hz with h | h <;> linarith

theorem closed_tips_attained : QuotientValues one crossing () (-1/2) ∧
    QuotientValues one crossing () 1 := by
  constructor <;> apply (reciprocal_exact _).mpr <;> norm_num

/-- Any convex enclosure has the false-positive central value 1/2. -/
theorem convex_enclosure_contains_half {C : Set ℝ} (hc : Convex ℝ C)
    (h : ∀ z, QuotientValues one crossing () z → z ∈ C) : (1/2 : ℝ) ∈ C := by
  have hn := h _ closed_tips_attained.1
  have hp := h _ closed_tips_attained.2
  have hh := hc hn hp (a := (1/3 : ℝ)) (b := (2/3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

theorem zero_only : ¬ ∃ z, QuotientValues one (fun (_ : Unit) y => y = 0) () z :=
  zero_only_absent (fun _ h => h)

theorem negative_touching : QuotientValues one (fun (_ : Unit) y => -2 ≤ y ∧ y ≤ 0) () (-1/2) := by
  refine ⟨1,-2,rfl,by norm_num,by norm_num,by norm_num⟩

theorem no_positive_touching_value {z : ℝ}
    (h : QuotientValues one (fun (_ : Unit) y => -2 ≤ y ∧ y ≤ 0) () z) : z ≤ -1/2 := by
  obtain ⟨x,y,rfl,hy,hn,rfl⟩ := h
  exact negative_bound (by norm_num) le_rfl hy.1 (lt_of_le_of_ne hy.2 hn)

theorem positive_touching : QuotientValues one (fun (_ : Unit) y => 0 ≤ y ∧ y ≤ 1) () 1 := by
  exact ⟨1,1,rfl,by norm_num,by norm_num,by norm_num⟩

theorem no_negative_touching_value {z : ℝ}
    (h : QuotientValues one (fun (_ : Unit) y => 0 ≤ y ∧ y ≤ 1) () z) : 1 ≤ z := by
  obtain ⟨x,y,rfl,hy,hn,rfl⟩ := h
  simpa using positive_bound (a := (1 : ℝ)) (d := 1) (x := 1)
    (by norm_num) le_rfl hy.2 (lt_of_le_of_ne hy.1 (Ne.symm hn))

theorem hole_preserved : ¬ ∃ z, QuotientValues
    (fun (_ : Unit) x => False ∧ one () x) (fun _ y => False ∧ crossing () y) () z := by
  rintro ⟨z,hz⟩
  exact ((restrict_iff one crossing (fun _ => False) () z).mp hz).1

/-- A denominator enclosure is not an exact image of a particular expression. -/
def sparse (_ : Unit) (y : ℝ) := y = -1 ∨ y = 1

theorem sparse_two_in_rays : (2 : ℝ) ∈ rays 1 1 1 := by
  right
  norm_num

theorem sparse_two_not_attained : ¬ QuotientValues one sparse () 2 := by
  rintro ⟨x,y,rfl,(rfl | rfl),_,h⟩ <;> norm_num at h

def reciprocalExpr := Expr.div (.const 1) .x

theorem expression_enclosed {x y z : ℝ} (hx : -2 ≤ x ∧ x ≤ 1)
    (hv : Value x y reciprocalExpr z) : z ∈ rays 1 2 1 := by
  apply expression_rays (e := .const 1) (f := .x)
    (by norm_num) (by norm_num) (by norm_num) _ _ hv
  · intro v h; cases h; norm_num
  · intro v h; cases h; exact hx

theorem expression_pole (y : ℝ) : ¬ ∃ z, Value 0 y reciprocalExpr z := by
  rintro ⟨z,hz⟩
  have h := (expression_iff 0 y (.const 1) .x z).mp hz
  obtain ⟨x,v,_,hv,hn,_⟩ := h
  cases hv
  exact hn rfl

/-- Nested operands stay in one coordinate environment; no new evaluator. -/
theorem nested_expression {x y z : ℝ} (hxy : -2 ≤ x-y ∧ x-y ≤ 1)
    (hv : Value x y (.div (.add (.const 1) (.const 1)) (.sub .x .y)) z) :
    z ∈ rays 2 2 1 := by
  apply expression_rays (e := .add (.const 1) (.const 1)) (f := .sub .x .y)
    (by norm_num) (by norm_num) (by norm_num) _ _ hv
  · intro w h
    cases h with
    | add h1 h2 => cases h1; cases h2; norm_num
  · intro w h
    cases h with
    | sub h1 h2 => cases h1; cases h2; exact hxy

#audit_namespace GeneralizedIntervalArithmetic.SplitQuotientChecks
end GeneralizedIntervalArithmetic.SplitQuotientChecks
