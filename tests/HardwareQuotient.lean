import HardwareQuotient
import AuditPolicy

namespace GeneralizedIntervalArithmetic.HardwareQuotientChecks
open HardwareEvaluator HardwareQuotient HardwareAddition

def cd (q : ℚ) : Option ℝ := some (q:ℝ)
def numerator : HardwareEvaluator.Polynomial ℚ := .const 1
def poleDen : HardwareEvaluator.Polynomial ℚ := .sub (.const (1/2)) .var
def pole : Expression ℚ := .binary .div (.polynomial numerator) (.polynomial poleDen)

theorem pole_den_at_midpoint : HardwareEvaluator.Value cd (1/2) poleDen 0 := by
  have h := HardwareEvaluator.Value.sub
    (HardwareEvaluator.Value.const (show cd (1/2) = some (1/2:ℝ) by norm_num [cd]))
    (HardwareEvaluator.Value.var (decode := cd) (x := (1/2:ℝ)))
  norm_num at h
  exact h

theorem pole_midpoint_undefined : ¬ ∃ v, HardwareQuotient.Value cd (1/2) pole v := by
  rintro ⟨v,hv⟩
  cases hv with
  | binary hn hd hne =>
    cases hd with
    | polynomial hd =>
      have hzero := polynomial_unique hd pole_den_at_midpoint
      exact hne hzero

theorem pole_has_defined_point : ∃ v, HardwareQuotient.Value cd 0 pole v := by
  have hn : HardwareEvaluator.Value cd 0 numerator 1 :=
    .const (show cd (1:ℚ) = some (1:ℝ) by norm_num [cd])
  have hd : HardwareEvaluator.Value cd 0 poleDen (1/2) := by
    have h := HardwareEvaluator.Value.sub
      (HardwareEvaluator.Value.const (show cd (1/2) = some (1/2:ℝ) by norm_num [cd]))
      (HardwareEvaluator.Value.var (decode := cd) (x := (0:ℝ)))
    norm_num at h
    exact h
  exact ⟨_,.binary (.polynomial hn) (.polynomial hd) (by norm_num [Defined])⟩

theorem acceptance_denominator {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (1/4:ℝ) ≤ 1/2-t*(1-t) ∧ 1/2-t*(1-t) ≤ 1/2 := by
  have h := parameter_bubble_bounds ht
  constructor <;> linarith

theorem acceptance_defined {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    Defined .div 1 (1/2-t*(1-t)) := by
  have h := acceptance_denominator ht
  change 1/2-t*(1-t) ≠ 0
  linarith

def lt (x y : ℚ) : Bool := decide (x<y)

theorem zero_endpoint_guard : HardwareDivision.awayZero lt 0 (⟨0,1⟩ : Bounds ℚ) = false := by
  norm_num [HardwareDivision.awayZero,lt]

theorem negative_guard : HardwareDivision.awayZero lt 0 (⟨-2,-1⟩ : Bounds ℚ) = true := by
  norm_num [HardwareDivision.awayZero,lt]

theorem zero_singleton_guard : HardwareDivision.awayZero lt 0 (⟨0,0⟩ : Bounds ℚ) = false := by
  norm_num [HardwareDivision.awayZero,lt]

theorem child_conflict_propagates :
    (step (m := Id) (fun _ _ => some (⟨1,1⟩ : Bounds ℚ)) lt min max
      ⟨some ⟨1,1⟩,.conflict⟩ ⟨some ⟨1,1⟩,.bound ⟨1,1⟩⟩).refined = .conflict := rfl

theorem ordinary_survives_failed_refinement :
    (step (m := Id) (fun _ _ => some (⟨1,1⟩ : Bounds ℚ)) lt min max
      ⟨some ⟨1,1⟩,.unknown⟩ ⟨some ⟨1,1⟩,.bound ⟨1,1⟩⟩).refined = .bound ⟨1,1⟩ := rfl

theorem both_fail_unknown :
    (step (m := Id) (fun _ _ => (none : Option (Bounds ℚ))) lt min max
      ⟨some ⟨1,1⟩,.bound ⟨1,1⟩⟩ ⟨some ⟨0,0⟩,.bound ⟨0,0⟩⟩).refined = .unknown := rfl

-- Any sound implementation must decline a whole-input certificate at the pole.
theorem pole_must_be_unknown {F : Type} {decode : F → Option ℝ}
    {leaf : HardwareEvaluator.Polynomial ℚ → Tracks F}
    {op : Operation → Bounds F → Bounds F → Option (Bounds F)}
    (hop : ∀ k, OperationSound decode k (op k))
    {cmp : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode cmp)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    (hl : AllLeaves (fun p => Certified cd decode (1/2) (.polynomial p) (leaf p)) pole) :
    (HardwareQuotient.eval (m := Id) leaf op cmp mn mx pole).refined = .unknown := by
  have h := eval_cert hop hc hn hm pole hl
  cases hr : (HardwareQuotient.eval (m := Id) leaf op cmp mn mx pole).refined with
  | unknown => rfl
  | conflict => exact False.elim (h.2.1 hr)
  | bound B =>
    obtain ⟨v,hv,_⟩ := success_defined h hr
    exact False.elim (pole_midpoint_undefined ⟨v,hv⟩)

#audit_namespace GeneralizedIntervalArithmetic.HardwareQuotientChecks
end GeneralizedIntervalArithmetic.HardwareQuotientChecks
