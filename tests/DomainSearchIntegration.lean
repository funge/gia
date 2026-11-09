import PointDomains
import AffineRegionSubdivision
import AuditPolicy

/- Independent cross-milestone client: no imports of milestone examples. -/
namespace GeneralizedIntervalArithmetic.DomainSearchIntegrationChecks

/-- Two independent domain analyses agree on all generated expressions at exact
rational points. This does not extend singleton completeness to interval inputs. -/
theorem point_guard_agreement (gs : List RationalAffineForm) (x y : ℚ) :
    (eval exactBackend (.point x) (.point y) (affineReciprocalSum gs)).isSome = true ↔
      affineGuardsHold gs (x,y) = true := by
  rw [eval_point_defined_iff,affine_guards_hold_iff]
  exact affine_sum_defined_iff gs ((x:ℝ),(y:ℝ))

def gx : RationalAffineForm := ⟨1,0,0⟩
def gy : RationalAffineForm := ⟨0,1,0⟩
def expression := affineReciprocalSum [gx,gy]
def wide : QInterval := ⟨-2,2,by norm_num⟩
def region : List RationalAffineForm := [⟨-1,0,-1⟩,⟨0,1,-1⟩]

/-- Independent exact zero set, not deduced from a classifier result. -/
theorem zero_set (x y : ℝ) : Value x y expression 0 ↔ x ≠ 0 ∧ y = -x := by
  constructor
  · intro hv
    have hn := (affine_sum_defined_iff [gx,gy] (x,y)).mp ⟨0,hv⟩
    have hx := hn gx (by simp)
    have hy := hn gy (by simp)
    simp [gx,gy,RationalAffineForm.value] at hx hy
    have he := value_eq_realValue hv
    simp [expression,affineReciprocalSum,RationalAffineForm.expression,
      Expr.realValue,gx,gy] at he
    have hs : x + y = 0 := by
      field_simp [hx,hy] at he
      linarith
    exact ⟨hx,by linarith⟩
  · rintro ⟨hx,rfl⟩
    have ha := affine_form_value gx (x,-x)
    have hb := affine_form_value gy (x,-x)
    simp [gx,gy,RationalAffineForm.value] at ha hb
    have hv := Value.add (Value.div (Value.const 1) ha hx)
      (Value.add (Value.div (Value.const 1) hb (neg_ne_zero.mpr hx)) (Value.const 0))
    simpa [expression,affineReciprocalSum] using hv

theorem point_root : (eval exactBackend (.point (-1)) (.point 1) expression).map (fun I => (I.lo,I.hi)) = some (0,0) := by decide +kernel

theorem point_pole : (eval exactBackend (.point 0) (.point 1) expression).isSome = false := by decide +kernel

theorem pole_undefined : ¬ ∃ z, Value 0 1 expression z := by
  intro h
  have hd := (eval_point_defined_iff 0 1 expression).mpr (by simpa using h)
  rw [point_pole] at hd
  contradiction

theorem wide_range_unavailable : (eval exactBackend wide wide expression).isSome = false := by decide +kernel

theorem wide_contains_actual_zero : Value (-1) 1 expression 0 :=
  (zero_set (-1) 1).mpr ⟨by norm_num,by norm_num⟩

theorem refined_present : refineAffineRegionBox 2 exactBackend wide wide [gx,gy] region = .present := by decide +kernel

theorem refined_semantics : HasAffineRegionRoot wide wide [gx,gy] region :=
  (refineAffineRegionBox_sound exactBackend_sound 2 wide wide [gx,gy] region).2 refined_present

/-- Removing the entire zero set invalidates every presence witness, despite
unchanged arithmetic and a positive certificate for the weaker region. -/
theorem extra_hole_excludes_all_roots : ¬ ∃ x y, wide.Contains x ∧ wide.Contains y ∧
    affineRegion region x y ∧ x + y ≠ 0 ∧ Value x y expression 0 := by
  rintro ⟨x,y,_,_,_,hole,hv⟩
  have he := ((zero_set x y).mp hv).2
  apply hole
  rw [he]
  ring

/-- Domain membership is not a certificate of a zero. -/
theorem defined_nonroot : affineGuardsHold [gx,gy] (1,1) = true ∧
    ¬ Value 1 1 expression 0 := by
  constructor
  · decide +kernel
  · rw [zero_set]
    norm_num

end GeneralizedIntervalArithmetic.DomainSearchIntegrationChecks
#audit_namespace GeneralizedIntervalArithmetic.DomainSearchIntegrationChecks
