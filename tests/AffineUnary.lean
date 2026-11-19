import AffineUnary
import AuditPolicy

namespace GeneralizedIntervalArithmetic.AffineUnaryChecks
open AffineUnary

def input : LinearInterval := .exact ⟨1/2,1⟩
def first : LinearInterval := ⟨⟨1/4,3/4⟩,⟨1/4,1⟩,by norm_num,by norm_num⟩
def second : LinearInterval := ⟨⟨1/16,5/16⟩,⟨1/16,1⟩,by norm_num,by norm_num⟩
def endpoints (I : LinearInterval) : ℚ × ℚ × ℚ × ℚ :=
  (I.lower.atZero,I.lower.atOne,I.upper.atZero,I.upper.atOne)

def uncertain : LinearInterval := ⟨⟨1/2,3/4⟩,⟨3/4,1⟩,by norm_num,by norm_num⟩
def uncertainResult : LinearInterval := ⟨⟨1/4,1/2⟩,⟨5/8,1⟩,by norm_num,by norm_num⟩

macro "compute_model" : tactic => `(tactic|
  norm_num [square,squareCandidate,select,propagate,image,input,first,second,uncertain,
    uncertainResult,endpoints,LinearInterval.exact,LinearInterval.hull,LinearInterval.constant,
    LinearInterval.mul,LinearInterval.join,LinearInterval.add,QInterval.point,QInterval.mul,
    QAffine.productBounds,QAffine.productChord,QAffine.curvature,QAffine.add])

theorem first_result : square input = some first := by compute_model

theorem second_result : square first = some second := by compute_model

theorem first_sound {t x : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : input.Contains t x) :
    first.Contains t (x^2) := square_sound first_result ht hx

theorem nested_sound {t x : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : input.Contains t x) :
    second.Contains t ((x^2)^2) := square_sound second_result ht (first_sound ht hx)

theorem midpoint_width :
    first.upper.value (1/2)-first.lower.value (1/2) = (1/8:ℝ) ∧
    ((input.hull.mul input.hull).hi:ℝ)-(input.hull.mul input.hull).lo = 3/4 := by
  norm_num [first,input,LinearInterval.exact,LinearInterval.hull,QInterval.mul,QAffine.value]

theorem uncertain_result : square uncertain = some uncertainResult := by compute_model

theorem uncertain_all_witnesses {t x : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hx : uncertain.Contains t x) : uncertainResult.Contains t (x^2) :=
  square_sound uncertain_result ht hx

theorem negative_slope_image : endpoints (image uncertain (-1) 2) = (5/4,1,3/2,5/4) := by compute_model

theorem singleton_square : square (.constant (.point (-2))) = some (.constant (.point 4)) := by compute_model

theorem mixed_sign_fallback : square (.exact ⟨-1,1⟩) =
    some (.constant ⟨-1,1,by norm_num⟩) := by compute_model

theorem ordinary_only : select (some (.point 2)) none = some (.constant (.point 2)) := rfl

theorem affine_only : select none (some first) = some first := rfl

theorem both_unavailable : select none none = none := rfl

theorem rejected_model_not_undefined : propagate input 0 1 0 0 = none ∧
    ∃ z : ℝ, z = (1/2:ℝ)^2 := by
  constructor
  · compute_model
  · exact ⟨_,rfl⟩

def punctured : DomainBounds ℝ := ⟨fun t => t ≠ 1/2,fun t => t ≠ 1/2,fun _ h => h⟩
def InputValues (t x : ℝ) : Prop :=
  t ∈ Set.Icc (0:ℝ) 1 ∧ t ≠ 1/2 ∧ x = (QAffine.mk (1/2) 1).value t

theorem input_domain : (input.onDomain punctured).Sound InputValues := by
  refine ⟨?_,?_,?_⟩
  · rintro t x ⟨ht,hh,hx⟩
    exact (linear_exact_contains _ _ _).mpr hx
  · rintro t x ⟨ht,hh,_⟩
    exact ⟨ht,hh⟩
  · rintro t ⟨ht,hh⟩
    exact ⟨_,ht,hh,rfl⟩

theorem punctured_nested_sound : (second.onDomain punctured).Sound
    (UnaryValues (UnaryValues InputValues (fun x z => z=x^2)) (fun x z => z=x^2)) :=
  square_domain_sound (square_domain_sound input_domain first_result) second_result

theorem hole_preserved : ¬ ∃ z,
    UnaryValues (UnaryValues InputValues (fun x z => z=x^2)) (fun x z => z=x^2) (1/2) z := by
  exact domain_absent punctured_nested_sound (by simp [LinearInterval.onDomain,punctured])

-- Carrying an unchanged domain through a genuinely partial function needs evidence.
theorem reciprocal_zero_prevents_totality :
    ¬ (∀ x : ℝ, x ∈ Set.Icc (-1:ℝ) 1 → ∃ z : ℝ, x ≠ 0 ∧ z=x⁻¹) := by
  intro h
  obtain ⟨z,hz,_⟩ := h 0 (by norm_num)
  exact hz rfl

#audit_namespace GeneralizedIntervalArithmetic.AffineUnaryChecks
end GeneralizedIntervalArithmetic.AffineUnaryChecks
