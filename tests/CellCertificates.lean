import AdaptiveCellCertification
import AuditPolicy

/- Fresh client: bounded cell checks, derived continuity, and actual root semantics. -/
namespace GeneralizedIntervalArithmetic.CellCertificateChecks

def X : LinearInterval := .exact ⟨0,1⟩
def Y : LinearInterval := .exact ⟨0,0⟩
def unit : QInterval := ⟨0,1,by norm_num⟩
def left : ParameterCell := ⟨unit.lowerHalf,by decide +kernel,by decide +kernel⟩
def right : ParameterCell := ⟨unit.upperHalf,by decide +kernel,by decide +kernel⟩
def expression : Expr := .div (.sub .x (.const (1/3)))
  (.add (.mul .x .x) (.const (1/10)))

theorem halves_cover : ParameterCover [left,right] := by
  intro t ht
  have hm : unit.Contains t := by simpa [unit,QInterval.Contains] using ht
  rcases (split_cover unit t).mp hm with hl | hr
  · exact ⟨left,by simp,hl⟩
  · exact ⟨right,by simp,hr⟩

theorem whole_unknown : (evalGuarded X Y expression).isNone := by decide +kernel

theorem two_calls_certify : checkCells X Y expression 2 [left,right] = ⟨.certified,2⟩ := by
  decide +kernel

theorem one_call_exhausts : checkCells X Y expression 1 [left,right] = ⟨.unknown,1⟩ := by
  decide +kernel

theorem zero_calls_unknown : checkCells X Y expression 0 [left,right] = ⟨.unknown,0⟩ := by
  decide +kernel

private theorem input_x (t : ℝ) : X.Contains t t := by
  simp [X,LinearInterval.Contains,LinearInterval.exact,QAffine.value]
private theorem input_y (t : ℝ) : Y.Contains t 0 := by
  simp [Y,LinearInterval.Contains,LinearInterval.exact,QAffine.value]

theorem derived_continuity_and_values :
    ContinuousOn (fun t => expression.realValue t 0) (Set.Icc (0:ℝ) 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, Value t 0 expression (expression.realValue t 0) := by
  apply checked_cover_continuous halves_cover
    (show (checkCells X Y expression 2 [left,right]).verdict = .certified from
      congrArg CellReport.verdict two_calls_certify)
    continuous_id.continuousOn continuous_const.continuousOn
    (fun t _ => input_x t) (fun t _ => input_y t)

theorem automatic_success :
    certifyCoveredCells X Y expression 2 [left,right] = ⟨.certified,2⟩ := by decide +kernel

theorem automatic_continuity_and_values :
    ContinuousOn (fun t => expression.realValue t 0) (Set.Icc (0:ℝ) 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, Value t 0 expression (expression.realValue t 0) :=
  certified_cells_continuous (congrArg CellReport.verdict automatic_success)
    continuous_id.continuousOn continuous_const.continuousOn
    (fun t _ => input_x t) (fun t _ => input_y t)

theorem adaptive_success :
    certifyAdaptiveCells X Y expression 1 2 = ⟨.certified,5⟩ := by decide +kernel

theorem adaptive_plan_size :
    (planAdaptiveCells X Y expression 1 ParameterCell.unit).cells.length = 2 ∧
    (planAdaptiveCells X Y expression 1 ParameterCell.unit).checked = 3 := by decide +kernel

theorem adaptive_depth_exhausted :
    certifyAdaptiveCells X Y expression 0 1 = ⟨.unknown,2⟩ ∧
    (planAdaptiveCells X Y expression 0 ParameterCell.unit).cells.length = 1 := by decide +kernel

theorem adaptive_validation_exhausted :
    certifyAdaptiveCells X Y expression 1 1 = ⟨.unknown,4⟩ ∧
    certifyAdaptiveCells X Y expression 1 0 = ⟨.unknown,3⟩ := by decide +kernel

theorem adaptive_stops_at_success :
    (planAdaptiveCells X Y (.const 7) 3 ParameterCell.unit).cells.length = 1 ∧
    certifyAdaptiveCells X Y (.const 7) 3 1 = ⟨.certified,2⟩ := by decide +kernel

theorem adaptive_continuity_and_values :
    ContinuousOn (fun t => expression.realValue t 0) (Set.Icc (0:ℝ) 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, Value t 0 expression (expression.realValue t 0) :=
  adaptive_certified_continuous (congrArg CellReport.verdict adaptive_success)
    continuous_id.continuousOn continuous_const.continuousOn
    (fun t _ => input_x t) (fun t _ => input_y t)

theorem actual_root : ∃ t ∈ Set.Icc (0:ℝ) 1, Value t 0 expression 0 := by
  obtain ⟨t,ht,hz⟩ := certified_curve_zero
    (L := QInterval.point (-10/3)) (U := QInterval.point (20/33))
    adaptive_continuity_and_values.1
    (by norm_num [QInterval.Contains,QInterval.point,Expr.realValue,expression])
    (by norm_num [QInterval.Contains,QInterval.point,Expr.realValue,expression])
    (by norm_num [QInterval.point]) (by norm_num [QInterval.point])
  exact ⟨t,ht,hz ▸ adaptive_continuity_and_values.2 t ht⟩

/-- There is a root even when the fuel-limited attempt returns unknown. -/
theorem exhausted_does_not_mean_no_root :
    (checkCells X Y expression 1 [left,right]).verdict = .unknown ∧
      ∃ t ∈ Set.Icc (0:ℝ) 1, Value t 0 expression 0 :=
  ⟨congrArg CellReport.verdict one_call_exhausts,actual_root⟩

def pole : Expr := .div (.const 1) (.sub .x (.const (1/2)))

theorem shared_boundary_pole_stops_early :
    checkCells X Y pole 10 [left,right] = ⟨.unknown,1⟩ := by decide +kernel

theorem pole_undefined_at_midpoint : ¬ ∃ z, Value (1/2) 0 pole z := by
  rintro ⟨z,hz⟩
  cases hz with
  | div _ hb hn =>
    cases hb with
    | sub hx hc =>
      cases hx
      cases hc
      norm_num at hn

theorem adaptive_pole_unknown :
    certifyAdaptiveCells X Y pole 1 2 = ⟨.unknown,4⟩ := by decide +kernel

/-- No refinement or validation budget can certify away the actual hole. -/
theorem adaptive_pole_never_certified (depth fuel : ℕ) :
    (certifyAdaptiveCells X Y pole depth fuel).verdict ≠ .certified := by
  intro h
  exact pole_undefined_at_midpoint (adaptive_certified_defined h
    (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1) (input_x (1/2)) (input_y (1/2)))

theorem adaptive_exhaustion_with_actual_root :
    (certifyAdaptiveCells X Y expression 0 1).verdict = .unknown ∧
      ∃ t ∈ Set.Icc (0:ℝ) 1, Value t 0 expression 0 :=
  ⟨congrArg CellReport.verdict adaptive_depth_exhausted.1,actual_root⟩

def gapLeft : ParameterCell := ⟨⟨0,1/4,by norm_num⟩,le_rfl,by norm_num⟩
def gapRight : ParameterCell := ⟨⟨3/4,1,by norm_num⟩,by norm_num,le_rfl⟩

theorem unchecked_gap_can_hide_pole :
    checkCells X Y pole 2 [gapLeft,gapRight] = ⟨.certified,2⟩ := by decide +kernel

theorem gap_is_not_a_cover : ¬ ParameterCover [gapLeft,gapRight] := by
  intro h
  obtain ⟨C,hC,hmem⟩ := h (1/2) (by norm_num)
  rcases List.mem_cons.mp hC with rfl | hC
  · norm_num [gapLeft,QInterval.Contains] at hmem
  · have he := List.mem_singleton.mp hC
    subst C
    norm_num [gapRight,QInterval.Contains] at hmem

theorem empty_list_checked : checkCells X Y pole 0 [] = ⟨.certified,0⟩ := rfl

theorem empty_list_not_cover : ¬ ParameterCover [] := by
  intro h
  obtain ⟨C,hC,_⟩ := h 0 (by norm_num)
  simp at hC

theorem automatic_gap_rejected :
    certifyCoveredCells X Y pole 2 [gapLeft,gapRight] = ⟨.unknown,0⟩ := by decide +kernel

theorem automatic_empty_rejected :
    certifyCoveredCells X Y pole 0 [] = ⟨.unknown,0⟩ := by decide +kernel

theorem automatic_fuel_exhausted :
    certifyCoveredCells X Y expression 1 [left,right] = ⟨.unknown,1⟩ := by decide +kernel

theorem automatic_pole_rejected :
    certifyCoveredCells X Y pole 10 [left,right] = ⟨.unknown,1⟩ := by decide +kernel

/-- Geometric checking is sound but deliberately order-sensitive, not complete. -/
theorem reversed_halves_still_cover : ParameterCover [right,left] := by
  intro t ht
  obtain ⟨C,hC,hmem⟩ := halves_cover t ht
  refine ⟨C,?_,hmem⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hC ⊢
  exact hC.symm

theorem reversed_halves_unknown :
    certifyCoveredCells X Y expression 2 [right,left] = ⟨.unknown,0⟩ := by decide +kernel

def wideLeft : ParameterCell := ⟨⟨0,3/4,by norm_num⟩,le_rfl,by norm_num⟩
def nested : ParameterCell := ⟨⟨1/4,1/2,by norm_num⟩,by norm_num,by norm_num⟩
def overlappingRight : ParameterCell := ⟨⟨2/3,1,by norm_num⟩,by norm_num,le_rfl⟩

theorem nested_overlap_accepted : cellsCoverFrom 0 [wideLeft,nested,overlappingRight] = true := by
  decide +kernel

theorem nested_overlap_cover : ParameterCover [wideLeft,nested,overlappingRight] :=
  checked_cells_cover nested_overlap_accepted

/-- A redundant tail is geometrically harmless, but arithmetic checks still use
fuel for every supplied cell. No minimal-cover extraction is claimed. -/
theorem redundant_cell_can_exhaust_fuel :
    certifyCoveredCells X Y expression 2 [left,right,right] = ⟨.unknown,2⟩ := by decide +kernel

end GeneralizedIntervalArithmetic.CellCertificateChecks

#audit_namespace GeneralizedIntervalArithmetic.CellCertificateChecks
