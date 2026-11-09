import CellContinuity
import ParameterRestrictionExamples
import SemanticContinuityExamples

namespace GeneralizedIntervalArithmetic.CellContinuityExamples

open ParameterRestrictionExamples (left right halves_cover left_endpoint_map right_endpoint_map)

def X : LinearInterval := .exact ⟨0,1⟩
def Y : LinearInterval := .exact ⟨0,0⟩
def curve : Expr := .div (.sub .x (.const (1/2))) (.add (.mul .x .x) (.const (1/8)))

theorem whole_unknown : (evalGuarded X Y curve).isNone = true := by decide +kernel

theorem cell_success (C : ParameterCell) (hC : C ∈ [left,right]) :
    (evalGuarded (X.reparam C) (Y.reparam C) curve).isSome := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
  rcases hC with rfl | rfl <;> decide +kernel

private theorem hx (t : ℝ) : X.Contains t t := by
  apply (linear_exact_contains _ _ _).mpr
  simp [QAffine.value]
private theorem hy (t : ℝ) : Y.Contains t 0 := by
  apply (linear_exact_contains _ _ _).mpr
  simp [QAffine.value]

theorem local_certificate (C : ParameterCell) (hC : C ∈ [left,right]) :
    ContinuousOn (fun s => curve.realValue (C.map s) 0) (Set.Icc (0:ℝ) 1) ∧
      ∀ s ∈ Set.Icc (0:ℝ) 1, Value (C.map s) 0 curve (curve.realValue (C.map s) 0) :=
  evalGuarded_reparam_continuous C continuousOn_id continuousOn_const
    (fun t _ => hx t) (fun t _ => hy t) (Option.some_get (cell_success C hC)).symm

theorem covered_continuous :
    ContinuousOn (fun t => curve.realValue t 0) (Set.Icc (0:ℝ) 1) :=
  parameter_cover_continuous halves_cover (fun C hC => (local_certificate C hC).1)

theorem covered_defined {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    Value t 0 curve (curve.realValue t 0) := by
  obtain ⟨C,hC,s,hs,he⟩ := parameter_cover_pullback halves_cover ht
  simpa [he] using (local_certificate C hC).2 s hs

/-- The midpoint is included in both certificates, not omitted between cells. -/
theorem boundary_values_agree :
    curve.realValue (left.map 1) 0 = curve.realValue (right.map 0) 0 := by
  rw [left_endpoint_map,right_endpoint_map]

theorem covered_defined_root : ∃ t ∈ Set.Icc (0:ℝ) 1, Value t 0 curve 0 := by
  obtain ⟨t,ht,hz⟩ := certified_curve_zero covered_continuous
    (L := .point (-4)) (U := .point (4/9))
    (by norm_num [QInterval.Contains,QInterval.point,curve,Expr.realValue])
    (by norm_num [QInterval.Contains,QInterval.point,curve,Expr.realValue])
    (by norm_num [QInterval.point]) (by norm_num [QInterval.point])
  exact ⟨t,ht,hz ▸ covered_defined ht⟩

/-- Two independently continuous branch functions are not a gluing certificate. -/
theorem separate_constants_continuous :
    ContinuousOn (fun _ : ℝ => (-1:ℝ)) (Set.Icc (0:ℝ) 1) ∧
    ContinuousOn (fun _ : ℝ => (1:ℝ)) (Set.Icc (0:ℝ) 1) :=
  ⟨continuousOn_const,continuousOn_const⟩

theorem incompatible_boundary : ¬ ∃ g : ℝ → ℝ,
    (∀ s ∈ Set.Icc (0:ℝ) 1, (-1:ℝ) = g (left.map s)) ∧
    (∀ s ∈ Set.Icc (0:ℝ) 1, (1:ℝ) = g (right.map s)) := by
  rintro ⟨g,hl,hr⟩
  have h1 := hl 1 (by norm_num)
  have h0 := hr 0 (by norm_num)
  rw [left_endpoint_map] at h1
  rw [right_endpoint_map] at h0
  linarith

def gapLeft : ParameterCell := ⟨⟨0,1/4,by norm_num⟩,by norm_num,by norm_num⟩
def gapRight : ParameterCell := ⟨⟨3/4,1,by norm_num⟩,by norm_num,by norm_num⟩

theorem missing_middle_not_cover : ¬ ParameterCover [gapLeft,gapRight] := by
  intro hc
  obtain ⟨C,hC,ht⟩ := hc (1/2) (by norm_num)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
  rcases hC with rfl | rfl <;> norm_num [gapLeft,gapRight,QInterval.Contains] at ht

/-- A point-cell certificate says nothing about points outside that cell. -/
theorem degenerate_cell_continuous (g : ℝ → ℝ) :
    ContinuousOn (fun s => g (ParameterRestrictionExamples.point.map s)) (Set.Icc (0:ℝ) 1) := by
  apply (parameter_cell_continuous_iff _ g).mp
  simp only [ParameterRestrictionExamples.point,QInterval.point]
  rw [Set.Icc_self]
  exact continuousOn_singleton g _

/-- Geometric coverage does not supply values at a semantic domain hole. -/
theorem hole_blocks_value_certificates :
    ¬ (∀ C ∈ [left,right], ∀ s ∈ Set.Icc (0:ℝ) 1,
      ∃ z, Value (C.map s) 0 SemanticContinuityExamples.pole z) := by
  intro h
  have hv := h left (by simp) 1 (by norm_num)
  rw [left_endpoint_map] at hv
  exact SemanticContinuityExamples.pole_midpoint_undefined hv

end GeneralizedIntervalArithmetic.CellContinuityExamples
