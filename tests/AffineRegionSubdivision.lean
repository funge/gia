import AffineRegionSubdivision
import AuditPolicy

namespace GeneralizedIntervalArithmetic.AffineRegionSubdivisionChecks

def gx : RationalAffineForm := ⟨1,0,0⟩
def gy : RationalAffineForm := ⟨0,1,0⟩
def region : List RationalAffineForm := [⟨-1,0,-1⟩,⟨0,1,-1⟩]
def wide : QInterval := ⟨-2,2,by norm_num⟩

theorem depth_zero_unknown : refineAffineRegionBox 0 exactBackend wide wide [gx,gy] region = .unknown := by decide +kernel

theorem depth_one_unknown : refineAffineRegionBox 1 exactBackend wide wide [gx,gy] region = .unknown := by decide +kernel

theorem depth_two_present : refineAffineRegionBox 2 exactBackend wide wide [gx,gy] region = .present := by decide +kernel

theorem certified_root : HasAffineRegionRoot wide wide [gx,gy] region :=
  (refineAffineRegionBox_sound exactBackend_sound 2 wide wide [gx,gy] region).2 depth_two_present

/-- An independent semantic witness, with no appeal to classification. -/
theorem actual_root : HasAffineRegionRoot wide wide [gx,gy] region := by
  refine ⟨-1,1,by norm_num [wide,QInterval.Contains],by norm_num [wide,QInterval.Contains],?_,?_⟩
  · norm_num [affineRegion,region,RationalAffineForm.value]
  · have hx := affine_form_value gx ((-1:ℝ),1)
    have hy := affine_form_value gy ((-1:ℝ),1)
    norm_num [gx,gy,RationalAffineForm.value] at hx hy
    have hv := Value.add (Value.div (Value.const 1) hx (by norm_num))
      (Value.add (Value.div (Value.const 1) hy (by norm_num)) (Value.const 0))
    simpa [affineReciprocalSum] using hv

theorem declined_unknown : refineAffineRegionBox 2 (fun _ => none) wide wide [gx,gy] region = .unknown := by decide +kernel

/-- An infeasible external region is not automatically a certificate of absence. -/
def impossible : List RationalAffineForm := [⟨1,0,-3⟩,⟨-1,0,-3⟩]

theorem impossible_unknown : refineAffineRegionBox 2 exactBackend wide wide [] impossible = .unknown := by decide +kernel

theorem impossible_has_no_points (x y : ℝ) : ¬ affineRegion impossible x y := by
  intro h
  have h₁ := h ⟨1,0,-3⟩ (by simp [impossible])
  have h₂ := h ⟨-1,0,-3⟩ (by simp [impossible])
  norm_num [RationalAffineForm.value] at h₁ h₂
  linarith

theorem arithmetic_empty : refineAffineRegionBox 2 exactBackend wide wide [⟨0,0,1⟩] region = .empty := by decide +kernel

theorem empty_semantics : ¬ HasAffineRegionRoot wide wide [⟨0,0,1⟩] region :=
  (refineAffineRegionBox_sound exactBackend_sound 2 wide wide [⟨0,0,1⟩] region).1 arithmetic_empty

/-- A split's shared boundary belongs to both children, with the same constraints. -/
def nonnegative : List RationalAffineForm := [⟨1,0,0⟩]

theorem boundary_root_both : HasAffineRegionRoot wide.lowerHalf wide [] nonnegative ∧
    HasAffineRegionRoot wide.upperHalf wide [] nonnegative := by
  have hb := split_boundary wide
  have he : affineRegion nonnegative 0 0 := by norm_num [affineRegion,nonnegative,RationalAffineForm.value]
  have hv : Value 0 0 (affineReciprocalSum []) 0 := by simpa [affineReciprocalSum] using (Value.const (x := (0:ℝ)) (y := 0) 0)
  have hy : wide.Contains (0:ℝ) := by norm_num [wide,QInterval.Contains]
  norm_num [wide,QInterval.midpoint] at hb
  exact ⟨⟨0,0,hb.1,hy,he,hv⟩,⟨0,0,hb.2,hy,he,hv⟩⟩

def point : QInterval := ⟨0,0,by norm_num⟩

theorem degenerate_pole_unknown : refineAffineRegionBox 3 exactBackend point point [gx] [] = .unknown := by decide +kernel

theorem degenerate_zero_present : refineAffineRegionBox 3 exactBackend point point [] [] = .present := by decide +kernel

end GeneralizedIntervalArithmetic.AffineRegionSubdivisionChecks
#audit_namespace GeneralizedIntervalArithmetic.AffineRegionSubdivisionChecks
