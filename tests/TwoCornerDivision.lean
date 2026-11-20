import TwoCornerDivision
import AuditPolicy
import Mathlib.Tactic.NormNum

namespace GeneralizedIntervalArithmetic.TwoCornerDivisionChecks
open TwoCornerDivision

macro "corners" : tactic => `(tactic| norm_num [select,positiveCorners,negativeCorners])

theorem six_rows :
    select 1 2 3 4 = some ((1,4),(2,3)) ∧
    select (-2) (-1) 3 4 = some ((-2,3),(-1,4)) ∧
    select (-1) 2 3 4 = some ((-1,3),(2,3)) ∧
    select 1 2 (-4) (-3) = some ((2,-3),(1,-4)) ∧
    select (-2) (-1) (-4) (-3) = some ((-1,-4),(-2,-3)) ∧
    select (-1) 2 (-4) (-3) = some ((2,-3),(-1,-3)) := by corners

theorem all_rows_extrema :
    min (min ((1:ℝ)/3) (1/4)) (min (2/3) (2/4)) = 1/4 ∧
    max (max ((-2:ℝ)/3) (-2/4)) (max (-1/3) (-1/4)) = -1/4 ∧
    min (min ((-1:ℝ)/3) (-1/4)) (min (2/3) (2/4)) = -1/3 ∧
    min (min ((1:ℝ)/(-4)) (1/(-3))) (min (2/(-4)) (2/(-3))) = -2/3 ∧
    max (max ((-2:ℝ)/(-4)) (-2/(-3))) (max (-1/(-4)) (-1/(-3))) = 2/3 ∧
    max (max ((-1:ℝ)/(-4)) (-1/(-3))) (max (2/(-4)) (2/(-3))) = 1/3 := by norm_num

theorem positive_witnessed :
    Encloses 1 2 3 4 ((1,4),(2,3)) ∧
    (∃ x y, (1 ≤ x ∧ x ≤ 2) ∧ (3 ≤ y ∧ y ≤ 4) ∧ y ≠ 0 ∧ x/y = (1:ℝ)/4) :=
  ⟨(select_spec six_rows.1).2.2.2.2.2,(extrema_attained six_rows.1).1⟩

theorem negative_witnessed :
    Encloses (-1) 2 (-4) (-3) ((2,-3),(-1,-3)) ∧
    (∃ x y, (-1 ≤ x ∧ x ≤ 2) ∧ (-4 ≤ y ∧ y ≤ -3) ∧ y ≠ 0 ∧ x/y = (1:ℝ)/3) := by
  have h := six_rows.2.2.2.2.2
  refine ⟨(select_spec h).2.2.2.2.2,?_⟩
  simpa using (extrema_attained h).2

theorem zero_boundaries :
    select 0 2 1 2 = some ((0,2),(2,1)) ∧
    select (-2) 0 1 2 = some ((-2,1),(0,2)) ∧
    select 0 2 (-2) (-1) = some ((2,-1),(0,-2)) ∧
    select (-2) 0 (-2) (-1) = some ((0,-2),(-2,-1)) := by corners

theorem zero_numerator :
    select 0 0 1 2 = some ((0,2),(0,1)) ∧
    select 0 0 (-2) (-1) = some ((0,-1),(0,-2)) := by corners

theorem singleton_denominator : select (-2) 3 2 2 = some ((-2,2),(3,2)) := by corners

theorem excluded_denominators :
    select 1 2 (-1) 1 = none ∧ select 1 2 0 1 = none ∧
    select 1 2 (-1) 0 = none ∧ select 1 2 0 0 = none := by corners

theorem rejected_is_not_empty : select 1 2 (-1) 1 = none ∧
    ∃ x y : ℝ, (1 ≤ x ∧ x ≤ 2) ∧ (-1 ≤ y ∧ y ≤ 1) ∧ y ≠ 0 ∧ x/y = 1 := by
  refine ⟨by corners,1,1,?_⟩
  norm_num

theorem reversed_rejected : select 2 1 1 2 = none ∧ select 1 2 2 1 = none := by corners

-- Signed zeros are real zero under the existing decode/comparison contract.
theorem decoded_zeros_rejected {F : Type} {decode : F → Option ℝ}
    {lt : F → F → Bool} {zero minusZero plusZero : F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hz : decode zero = some 0) (hm : decode minusZero = some 0) (hp : decode plusZero = some 0) :
    HardwareDivision.awayZero lt zero ⟨minusZero,plusZero⟩ = false := by
  have h1 := hc plusZero zero 0 0 hp hz
  have h2 := hc zero minusZero 0 0 hz hm
  simp only [lt_self_iff_false, iff_false] at h1 h2
  simp [HardwareDivision.awayZero, Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h2]

noncomputable def realLt (a b : ℝ) : Bool := decide (a < b)
theorem real_comparison : HardwareDivision.CompareSound some realLt := by
  simp [HardwareDivision.CompareSound,realLt]

theorem exact_call (a b : ℝ) : HardwareDivision.CallSound some a b (some (a/b,a/b)) := by
  simp [HardwareDivision.CallSound,HardwareMultiplication.ResultSound]

theorem failed_call (a b : ℝ) : HardwareDivision.CallSound some a b none := by
  simp [HardwareDivision.CallSound,HardwareMultiplication.ResultSound]

theorem loose_omitted_call : HardwareDivision.CallSound some (1:ℝ) 1 (some (-10,10)) := by
  norm_num [HardwareDivision.CallSound,HardwareMultiplication.ResultSound]

theorem two_calls_enclose {x y : ℝ} (hx : 1 ≤ x ∧ x ≤ 2) (hy : 1 ≤ y ∧ y ≤ 2) :
    HardwareAddition.Contains some ⟨(1:ℝ)/2,2⟩ (x/y) ∧ y ≠ 0 := by
  apply assemble_selected_encloses (show select 1 2 1 2 = some ((1,2),(2,1)) by corners)
    (decode := some) (ln := (1:ℝ)) (ld := 2) (un := 2) (ud := 1)
    rfl rfl rfl rfl (exact_call 1 2) (exact_call 2 1) ?_ hx hy
  norm_num [HardwareAddition.assemble]

/-- For I=J=[1,2], (1,2) is retained, not omitted. The omitted (1,1)
can fail without violating CallSound. Four-call assembly then fails. -/
theorem omission_changes_availability :
    HardwareMultiplication.assembleFour min max (none : Option (ℝ × ℝ))
      (some (1/2,1/2)) (some (2,2)) (some (1,1)) = none ∧
    HardwareAddition.assemble (some ((1:ℝ)/2,1/2)) (some (2,2)) = some ⟨1/2,2⟩ := by
  norm_num [HardwareMultiplication.assembleFour,HardwareAddition.assemble]

theorem omission_changes_width :
    HardwareMultiplication.assembleFour min max (some ((-10:ℝ),10))
      (some (1/2,1/2)) (some (2,2)) (some (1,1)) = some ⟨-10,10⟩ ∧
    HardwareAddition.assemble (some ((1:ℝ)/2,1/2)) (some (2,2)) = some ⟨1/2,2⟩ := by
  norm_num [HardwareMultiplication.assembleFour,HardwareAddition.assemble]

theorem selected_failure_unknown :
    HardwareAddition.assemble (none : Option (ℝ × ℝ)) (some (2,2)) = none ∧
    HardwareAddition.assemble (some ((1:ℝ)/2,1/2)) none = none := by constructor <;> rfl

#audit_namespace GeneralizedIntervalArithmetic.TwoCornerDivisionChecks
end GeneralizedIntervalArithmetic.TwoCornerDivisionChecks
