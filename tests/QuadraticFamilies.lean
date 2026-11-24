import QuadraticFamilies
import AuditPolicy
namespace GeneralizedIntervalArithmetic.QuadraticFamiliesChecks
open QuadraticFamilies

noncomputable def x : MultiAffineFamilies.Form 1 := ⟨0,fun _=>1⟩
noncomputable def oneMinusX : MultiAffineFamilies.Form 1 := ⟨1,fun _=> -1⟩
noncomputable def bubble : Form 1 := product x oneMinusX

theorem bubble_value (t : Fin 1 → ℝ) : bubble.value t = t 0*(1-t 0) := by
  rw [bubble,product_value]
  simp [x,oneMinusX,MultiAffineFamilies.Form.value,sub_eq_add_neg]

theorem corners_miss_maximum :
    bubble.value (fun _=>0) = 0 ∧ bubble.value (fun _=>1) = 0 ∧
    bubble.value (fun _=>1/2) = 1/4 := by norm_num [bubble_value]

theorem coarse_demotion_not_optimal : bubble.lo = -1 ∧ bubble.hi = 1 := by
  norm_num [bubble,product,x,oneMinusX,Form.lo,Form.hi,
    MultiAffineFamilies.Form.lo,MultiAffineFamilies.Form.hi]

theorem bubble_exact_extrema {t : Fin 1 → ℝ} (ht : MultiAffineFamilies.Cube t) :
    0 ≤ bubble.value t ∧ bubble.value t ≤ 1/4 := by
  rw [bubble_value]
  exact parameter_bubble_bounds (ht 0)

theorem reused_chord_bound {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (QAffine.productBounds ⟨0,1⟩ ⟨1,0⟩).Contains t (bubble.value (fun _=>t)) := by
  have h := product_chord_demotion (a:=⟨0,1⟩) (b:=⟨1,0⟩) ht
  simpa [bubble,x,oneMinusX,MultiAffineFamilies.fromQAffine] using h

theorem chord_is_quarter :
    (QAffine.productBounds ⟨0,1⟩ ⟨1,0⟩).hull.lo = 0 ∧
    (QAffine.productBounds ⟨0,1⟩ ⟨1,0⟩).hull.hi = 1/4 := by
  norm_num [QAffine.productBounds,QAffine.curvature,LinearInterval.hull]

noncomputable def first : MultiAffineFamilies.Form 2 := ⟨0,![1,0]⟩
noncomputable def second : MultiAffineFamilies.Form 2 := ⟨0,![0,1]⟩

theorem cross_term (t : Fin 2 → ℝ) : (product first second).value t = t 0*t 1 := by
  rw [product_value]
  simp [first,second,MultiAffineFamilies.Form.value,Fin.sum_univ_two]

theorem independent_parameters_are_not_product_semantics :
    (product x oneMinusX).value (fun _=>1) = 0 ∧
    x.value (fun _=>1)*oneMinusX.value (fun _=>0) = 1 := by
  norm_num [product_value,x,oneMinusX,MultiAffineFamilies.Form.value]

theorem cancellation (a : Form 2) (t) : (a.sub a).value t = 0 := by
  rw [sub_value]; ring

noncomputable def exactBubble : Bounds 1 := ⟨bubble,bubble,fun _ _=>le_rfl⟩
theorem projection_sound {t z} (ht : MultiAffineFamilies.Cube t)
    (hz : exactBubble.Contains t z) : exactBubble.constantHull.Contains z :=
  demotion_encloses _ ht hz

theorem quadratic_bound_collapse_inside :
    (ofCoefficients 0 0 0).value (fun _=>0) ≤ (ofCoefficients 0 (-1) 1).value (fun _=>0) ∧
    (ofCoefficients 0 0 0).value (fun _=>1) ≤ (ofCoefficients 0 (-1) 1).value (fun _=>1) ∧
    ¬ (ofCoefficients 0 0 0).value (fun _=>1/2) ≤ (ofCoefficients 0 (-1) 1).value (fun _=>1/2) := by
  norm_num [coefficients_value]

/-- Multiplying arbitrary quadratic forms is not closed in this carrier. -/
theorem fourth_power_not_quadratic :
    ¬ ∃ p q r : ℚ, ∀ t ∈ Set.Icc (0:ℝ) 1,
      (ofCoefficients p q r).value (fun _=>t) = t^4 := by
  rintro ⟨p,q,r,h⟩
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have hm := h (1/2) (by norm_num)
  have hq := h (1/4) (by norm_num)
  norm_num [coefficients_value] at h0 h1 hm hq
  simp only [h0,Rat.cast_zero,zero_add] at h1 hm hq
  linarith

end GeneralizedIntervalArithmetic.QuadraticFamiliesChecks
#audit_namespace GeneralizedIntervalArithmetic.QuadraticFamiliesChecks
