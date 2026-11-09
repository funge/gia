import AffineRegions
import AuditPolicy

namespace GeneralizedIntervalArithmetic.AffineRegionChecks

def gx : RationalAffineForm := ⟨1,0,0⟩
def gy : RationalAffineForm := ⟨0,1,0⟩
def region : List RationalAffineForm := [⟨-1,0,-1⟩,⟨0,1,-1⟩]
def box : QInterval := ⟨-2,2,by norm_num⟩

theorem checked_inclusion : classifyAffineRegionSegment region (-1,2) (-2,1) = .yes :=
  by decide +kernel

theorem concrete_region (x y : ℝ) : affineRegion region x y ↔ x ≤ -1 ∧ 1 ≤ y := by
  simp [affineRegion,region,RationalAffineForm.value]
  intro _
  constructor <;> intro h <;> linarith

theorem checked_presence : ∃ x y, box.Contains x ∧ box.Contains y ∧
    affineRegion region x y ∧ Value x y (affineReciprocalSum [gx,gy]) 0 :=
  certifyAffineSegment_in_region exactBackend_sound checked_inclusion (by decide +kernel)

theorem boundary_yes : classifyAffineRegionSegment [gx] (0,0) (1,0) = .yes := by decide +kernel

theorem boundary_included : affineRegion [gx] 0 0 := by
  simp [affineRegion,gx,RationalAffineForm.value]

theorem mixed_unknown : classifyAffineRegionSegment [gx] (-1,0) (1,0) = .unknown :=
  by decide +kernel

theorem mixed_membership : ¬ affineRegion [gx] (-1) 0 ∧ affineRegion [gx] 1 0 := by
  norm_num [affineRegion,gx,RationalAffineForm.value]

theorem endpoint_contact_unknown : classifyAffineRegionSegment [gx] (-1,0) (0,0) = .unknown :=
  by decide +kernel

theorem outside_no : classifyAffineRegionSegment [gx] (-2,0) (-1,0) = .no := by decide +kernel

theorem outside_semantics : ∀ t ∈ Set.Icc (0:ℝ) 1,
    ¬ affineRegion [gx] (segment (-2) (-1) t) (segment 0 0 t) := by
  have h := affine_region_query_sound [gx] (-2,0) (-1,0)
  simpa [outside_no,BranchSound] using h

/-- No single constraint excludes the whole path, but their conjunction is empty. -/
def incompatible : List RationalAffineForm := [gx,⟨-1,0,-1⟩]

theorem incompatible_unknown : classifyAffineRegionSegment incompatible (-2,0) (1,0) = .unknown :=
  by decide +kernel

theorem incompatible_empty (x y : ℝ) : ¬ affineRegion incompatible x y := by
  simp [affineRegion,incompatible,gx,RationalAffineForm.value]
  intro hx
  linarith

theorem empty_list_yes (a b : ℚ × ℚ) : classifyAffineRegionSegment [] a b = .yes := rfl

theorem degenerate_yes : classifyAffineRegionSegment region (-1,1) (-1,1) = .yes :=
  by decide +kernel

theorem zero_constraint_yes : classifyAffineRegionSegment [⟨0,0,0⟩] (-1,2) (3,-4) = .yes :=
  by decide +kernel

/-- Path exclusion cannot be promoted to absence throughout the input box. -/
def otherRegion : List RationalAffineForm := [⟨1,0,-1⟩]

theorem other_path_no : classifyAffineRegionSegment otherRegion (-1,2) (-2,1) = .no :=
  by decide +kernel

theorem other_box_root : box.Contains (1:ℝ) ∧ box.Contains (-1:ℝ) ∧
    affineRegion otherRegion 1 (-1) ∧ Value 1 (-1) (affineReciprocalSum [gx,gy]) 0 := by
  refine ⟨by norm_num [box,QInterval.Contains],by norm_num [box,QInterval.Contains],?_,?_⟩
  · simp [affineRegion,otherRegion,RationalAffineForm.value]
  · have hx := affine_form_value gx ((1:ℝ),-1)
    have hy := affine_form_value gy ((1:ℝ),-1)
    norm_num [gx,gy,RationalAffineForm.value] at hx hy
    have hv := Value.add (Value.div (Value.const 1) hx (by norm_num))
      (Value.add (Value.div (Value.const 1) hy (by norm_num)) (Value.const 0))
    norm_num at hv
    simpa [affineReciprocalSum,gx,gy] using hv

/-- Additional external holes are not covered by the constraint-list certificate. -/
theorem extra_hole_excludes_root (x y : ℝ)
    (h : (affineReciprocalSum [gx,gy]).realValue x y ≠ 0) :
    ¬ Value x y (affineReciprocalSum [gx,gy]) 0 := by
  intro hv
  exact h (value_eq_realValue hv).symm

end GeneralizedIntervalArithmetic.AffineRegionChecks
#audit_namespace GeneralizedIntervalArithmetic.AffineRegionChecks
