import Mathlib.Analysis.Calculus.Deriv.Pow
import TangentBounds
import AuditPolicy

namespace GeneralizedIntervalArithmetic.TangentChecks
open EndpointChords TangentBounds

theorem square_convex : ConvexOn ℝ (Set.Icc 0 1) (fun x : ℝ => x^2) :=
  (convexOn_pow 2).subset (fun _ hx => hx.1) (convex_Icc _ _)

theorem square_derivative (p : ℝ) : HasDerivAt (fun x : ℝ => x^2) (2*p) p := by
  convert (hasDerivAt_id p).pow 2 using 1; norm_num

theorem midpoint_sandwich {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    t-1/4 ≤ t^2 ∧ t^2 ≤ t := by
  have hd : HasDerivWithinAt (fun x : ℝ => x^2) 1 (Set.Icc 0 1) (1/2) := by
    convert (square_derivative (1/2)).hasDerivWithinAt using 1; norm_num
  have h := convex_sandwich square_convex (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1) hd ht
  norm_num [blend,tangent] at h
  constructor <;> linarith [h.1,h.2]

theorem negative_square_upper {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    -x^2 ≤ 1/4-x := by
  have hf : ConcaveOn ℝ (Set.Icc 0 1) (fun x : ℝ => -x^2) :=
    neg_concaveOn_iff.mpr square_convex
  have hd : HasDerivWithinAt (fun x : ℝ => -x^2) (-1) (Set.Icc 0 1) (1/2) := by
    convert (square_derivative (1/2)).neg.hasDerivWithinAt using 1; norm_num
  have h := TangentBounds.concave_upper hf (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1) hd hx
  norm_num [tangent] at h
  linarith

theorem endpoint_tangent {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : 0 ≤ x^2 := by
  have h := TangentBounds.convex_lower square_convex
    (by norm_num : (0:ℝ) ∈ Set.Icc 0 1) (square_derivative 0).hasDerivWithinAt hx
  simpa [tangent] using h

theorem certified_square_lower {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    blend (-1/2) (1/2) t ≤ t^2 := by
  have h := TangentBounds.outward_lower square_convex
    (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)
    (square_derivative (1/2)).hasDerivWithinAt
    (show (-1/2:ℝ) ≤ tangent (fun x : ℝ => x^2) (1/2) (2*(1/2)) 0 by norm_num [tangent])
    (show tangent (fun x : ℝ => x^2) (1/2) (2*(1/2)) 1 ≥ (1/2:ℝ) by norm_num [tangent]) ht
  simpa [blend] using h

theorem singleton_arbitrary_slope : tangent (fun x : ℝ => x^2) 3 123 3 = 9 := by
  norm_num [tangent]

-- Tangents at distinct contacts need not dominate each other pointwise.
theorem tangents_cross :
    tangent (fun x : ℝ => -x^2) 0 0 0 < tangent (fun x : ℝ => -x^2) 1 (-2) 0 ∧
    tangent (fun x : ℝ => -x^2) 1 (-2) 1 < tangent (fun x : ℝ => -x^2) 0 0 1 := by
  norm_num [tangent]

-- Rounding the derivative upward alone does not certify a whole tangent bound.
theorem rounded_slope_wrong_left :
    ¬ (0:ℝ) ≤ tangent (fun x : ℝ => x) (1/2) 2 0 := by norm_num [tangent]

theorem rounded_slope_wrong_right :
    ¬ tangent (fun x : ℝ => x) (1/2) 2 1 ≤ (1:ℝ) := by norm_num [tangent]

#audit_namespace GeneralizedIntervalArithmetic.TangentChecks
end GeneralizedIntervalArithmetic.TangentChecks
