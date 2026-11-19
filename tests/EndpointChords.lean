import EndpointChords
import AuditPolicy

namespace GeneralizedIntervalArithmetic.EndpointChordChecks
open EndpointChords

theorem square_convex : ConvexOn ℝ (Set.Icc 0 1) (fun x : ℝ => x^2) :=
  (convexOn_pow 2).subset (fun _ hx => hx.1) (convex_Icc _ _)

theorem square_chord {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : t^2 ≤ t := by
  have h := convex_upper (by norm_num : (0:ℝ) ≤ 1) square_convex ht
  simpa [blend] using h

theorem outward_square {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    t^2 ≤ (QAffine.value ⟨1/10,11/10⟩ t) := by
  have h := qaffine_upper (f := fun x : ℝ => x^2) (a := 0) (b := 1)
    ⟨1/10,11/10⟩ (by norm_num) square_convex (by norm_num) (by norm_num) ht
  simpa [blend] using h

-- Outward certification does not imply exact endpoint optimality.
theorem outward_not_least :
    blend (0:ℝ) 1 (1/2) < QAffine.value ⟨1/10,11/10⟩ (1/2) := by
  norm_num [blend,QAffine.value]

theorem wrong_side_rejected : ¬ blend (0:ℝ) 1 (1/2) ≤ (1/2:ℝ)^2 := by
  norm_num [blend]

theorem extrapolation_rejected : ¬ (2:ℝ)^2 ≤ blend 0 1 2 := by norm_num [blend]

theorem singleton_no_curvature_needed (f : ℝ → ℝ) (t : ℝ) :
    blend (f 3) (f 3) t = f 3 := blend_singleton _ _

theorem singleton_parameter : ∃ t ∈ Set.Icc (0:ℝ) 1, blend 3 3 t = 3 :=
  parameter_exists ⟨le_rfl,le_rfl⟩

theorem cubic_whole_source {α x : ℝ} (hα : α ∈ Set.Icc (0:ℝ) 1)
    (hx : x ∈ Set.Icc (-2+α) (4-α)) : -8+7*α ≤ x^3 ∧ x^3 ≤ 64-37*α :=
  cubic_source_enclosure hα hx

theorem cubic_zero_endpoints : (-2:ℝ)^3 = -8 ∧ (4:ℝ)^3 = 64 := by norm_num

theorem cubic_one_endpoints : (-1:ℝ)^3 = -8+7 ∧ (3:ℝ)^3 = 64-37 := by norm_num

theorem cubic_interior_slack :
    (-8+7*(1/2:ℝ)) < (-2+(1/2:ℝ))^3 ∧
    (4-(1/2:ℝ))^3 < 64-37*(1/2:ℝ) := by norm_num

#audit_namespace GeneralizedIntervalArithmetic.EndpointChordChecks
end GeneralizedIntervalArithmetic.EndpointChordChecks
