import AffineRegionSearch
import AuditPolicy

namespace GeneralizedIntervalArithmetic.AffineRegionSearchChecks

def gx : RationalAffineForm := ⟨1,0,0⟩
def gy : RationalAffineForm := ⟨0,1,0⟩
def region : List RationalAffineForm := [⟨-1,0,-1⟩,⟨0,1,-1⟩]
def X : QInterval := ⟨-2,-1,by norm_num⟩
def Y : QInterval := ⟨1,2,by norm_num⟩
def wide : QInterval := ⟨-2,2,by norm_num⟩
def good : SegmentCandidate := ((-1,2),(-2,1))
def bad : SegmentCandidate := ((0,0),(1,1))

theorem automatic_present : classifyAffineRegionBox exactBackend X Y [gx,gy] region = .present :=
  by decide +kernel

theorem automatic_semantics : ∃ x y, X.Contains x ∧ Y.Contains y ∧ affineRegion region x y ∧
    Value x y (affineReciprocalSum [gx,gy]) 0 :=
  (affine_region_box_sound exactBackend_sound X Y [gx,gy] region).2 automatic_present

theorem first_good : searchAffineRegionSegments exactBackend wide wide [gx,gy] region
    [bad,good,good] = some good := by decide +kernel

theorem candidate_member : good ∈ ([bad,good,good] : List SegmentCandidate) :=
  affine_region_search_mem first_good

theorem reverse_orientation :
    certifyAffineSegment exactBackend wide wide [gx,gy] good.2 good.1 = false ∧
    certifyAffineRegionCandidate exactBackend wide wide [gx,gy] region (good.2,good.1) = true :=
  by decide +kernel

/-- Independently construct real zeros, without using any search soundness theorem. -/
theorem opposite_root (q : ℝ) (hq : q ≠ 0) :
    Value q (-q) (affineReciprocalSum [gx,gy]) 0 := by
  have hx := affine_form_value gx (q,-q)
  have hy := affine_form_value gy (q,-q)
  simp [gx,gy,RationalAffineForm.value] at hx hy
  have hv := Value.add (Value.div (Value.const 1) hx hq)
    (Value.add (Value.div (Value.const 1) hy (neg_ne_zero.mpr hq)) (Value.const 0))
  simpa [affineReciprocalSum,gx,gy] using hv

theorem missed_root : wide.Contains (-1:ℝ) ∧ wide.Contains (1:ℝ) ∧
    affineRegion region (-1) 1 ∧ Value (-1) 1 (affineReciprocalSum [gx,gy]) 0 := by
  refine ⟨by norm_num [wide,QInterval.Contains],by norm_num [wide,QInterval.Contains],?_,?_⟩
  · norm_num [affineRegion,region,RationalAffineForm.value]
  · simpa using opposite_root (-1) (by norm_num)

theorem automatic_unknown : classifyAffineRegionBox exactBackend wide wide [gx,gy] region = .unknown :=
  by decide +kernel

theorem supplied_present : classifyAffineRegionSearch exactBackend wide wide [gx,gy] region
    [good] = .present := by decide +kernel

theorem empty_search_unknown : classifyAffineRegionSearch exactBackend wide wide [gx,gy] region
    [] = .unknown := by decide +kernel

theorem declined_unknown : classifyAffineRegionBox (fun _ => none) X Y [gx,gy] region = .unknown :=
  by decide +kernel

/-- Even a pole-free constant expression can be missed when the policy's center
is outside the external region. Rejected paths do not imply box absence. -/
def rightRegion : List RationalAffineForm := [⟨1,0,-1⟩]

theorem outside_center_unknown : classifyAffineRegionBox exactBackend wide wide [] rightRegion = .unknown :=
  by decide +kernel

theorem constant_root_in_region : wide.Contains (1:ℝ) ∧ wide.Contains (0:ℝ) ∧
    affineRegion rightRegion 1 0 ∧ Value 1 0 (affineReciprocalSum []) 0 := by
  refine ⟨by norm_num [wide,QInterval.Contains],by norm_num [wide,QInterval.Contains],?_,?_⟩
  · norm_num [affineRegion,rightRegion,RationalAffineForm.value]
  · simpa [affineReciprocalSum] using (Value.const (x := (1:ℝ)) (y := 0) 0)

theorem excluded_path_unknown : classifyAffineRegionSearch exactBackend wide wide [] rightRegion
    [((-2,0),(-1,0))] = .unknown := by decide +kernel

theorem arithmetic_empty : classifyAffineRegionBox exactBackend wide wide [⟨0,0,1⟩] region = .empty :=
  by decide +kernel

theorem empty_semantics : ¬ ∃ x y, wide.Contains x ∧ wide.Contains y ∧ affineRegion region x y ∧
    Value x y (affineReciprocalSum [⟨0,0,1⟩]) 0 :=
  (affine_region_box_sound exactBackend_sound wide wide [⟨0,0,1⟩] region).1 arithmetic_empty

end GeneralizedIntervalArithmetic.AffineRegionSearchChecks
#audit_namespace GeneralizedIntervalArithmetic.AffineRegionSearchChecks
