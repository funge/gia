import AffineSegmentDomains
import AuditPolicy

namespace GeneralizedIntervalArithmetic.AffineSegmentChecks

def gx : RationalAffineForm := ⟨1,0,0⟩
def gy : RationalAffineForm := ⟨0,1,0⟩
def X : QInterval := ⟨-2,2,by norm_num⟩
def Y : QInterval := ⟨1,2,by norm_num⟩
def a : ℚ × ℚ := (-1,2)
def b : ℚ × ℚ := (-2,1)

theorem old_unknown : classifyWithSegment exactBackend X Y
    (affineReciprocalSum [gx,gy]) a b = .unknown := by decide +kernel

theorem improved : classifyAffineWithSegment exactBackend X Y [gx,gy] a b = .present :=
  by decide +kernel

theorem improved_semantics : ∃ x y, X.Contains x ∧ Y.Contains y ∧
    Value x y (affineReciprocalSum [gx,gy]) 0 :=
  classifyAffineWithSegment_present exactBackend_sound improved

/-- Independent actual zero, not obtained from the checker theorem. -/
theorem explicit_root : Value (-3/2:ℝ) (3/2:ℝ) (affineReciprocalSum [gx,gy]) 0 := by
  have hx := affine_form_value gx ((-3/2:ℝ),(3/2:ℝ))
  have hy := affine_form_value gy ((-3/2:ℝ),(3/2:ℝ))
  norm_num [gx,gy,RationalAffineForm.value] at hx hy
  have vx := Value.div (Value.const 1) hx (by norm_num)
  have vy := Value.div (Value.const 1) hy (by norm_num)
  have hv := Value.add vx (Value.add vy (Value.const 0))
  norm_num at hv
  simpa [affineReciprocalSum,gx,gy,neg_div] using hv

theorem off_segment_pole : ¬ ∃ z, Value 0 1 (affineReciprocalSum [gx,gy]) z := by
  rw [affine_sum_defined_iff [gx,gy] (0,1)]
  simp [gx,gy,RationalAffineForm.value]

theorem crossing_unknown : classifyAffineWithSegment exactBackend X Y [gx]
    (-1,1) (1,1) = .unknown := by decide +kernel

theorem crossing_endpoints_defined : affineGuardsHold [gx] (-1,1) = true ∧
    affineGuardsHold [gx] (1,1) = true := by decide +kernel

theorem crossing_not_safe : affineSegmentSafe [gx] (-1,1) (1,1) = false :=
  by decide +kernel

/-- The apparent sign change is a pole, and this expression has no zero anywhere. -/
theorem reciprocal_no_zero (x y : ℝ) : ¬ Value x y (affineReciprocalSum [gx]) 0 := by
  intro hv
  have he := value_eq_realValue hv
  have hd := (affine_sum_defined_iff [gx] (x,y)).mp ⟨0,hv⟩ gx (by simp)
  simp [gx,RationalAffineForm.value] at hd
  simp [affineReciprocalSum,RationalAffineForm.expression,gx,Expr.realValue] at he
  exact hd he.symm

theorem endpoint_pole_unknown : classifyAffineWithSegment exactBackend X Y [gx]
    (0,1) (1,1) = .unknown := by decide +kernel

theorem outside_rejected : certifyAffineSegment exactBackend X Y [gx,gy]
    (-3,2) (-2,1) = false := by decide +kernel

theorem declining_unknown : classifyAffineWithSegment (fun _ => none) X Y [gx,gy]
    a b = .unknown := by decide +kernel

/-- External domains are not part of this checker contract. -/
theorem external_hole_removes_zeros (x y : ℝ)
    (h : (affineReciprocalSum [gx,gy]).realValue x y ≠ 0) :
    ¬ Value x y (affineReciprocalSum [gx,gy]) 0 := by
  intro hv
  exact h (value_eq_realValue hv).symm

/-- Use the new converse on actual semantics, not just a Boolean reduction. -/
theorem crossing_has_hole : ∃ t ∈ Set.Icc (0:ℝ) 1, ¬ ∃ z,
    Value (segment (-1) 1 t) (segment 1 1 t) (affineReciprocalSum [gx]) z := by
  simpa using (affine_segment_unsafe_iff_hole [gx] (-1,1) (1,1)).mp crossing_not_safe

theorem safe_degenerate : affineSegmentSafe [gx] (1,1) (1,1) = true := by decide +kernel

theorem unsafe_degenerate : affineSegmentSafe [gx] (0,1) (0,1) = false := by decide +kernel

theorem empty_guards_defined (a b : ℚ × ℚ) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ z,
      Value (segment a.1 b.1 t) (segment a.2 b.2 t) (affineReciprocalSum []) z :=
  (affine_segment_safe_iff_defined [] a b).mp rfl

/-- A hole and an actual zero can coexist on the same segment. -/
theorem unsafe_with_root : affineSegmentSafe [gx,gy] (-1,1) (1,-1) = false ∧
    Value (-1:ℝ) 1 (affineReciprocalSum [gx,gy]) 0 := by
  constructor
  · decide +kernel
  · have hx := affine_form_value gx ((-1:ℝ),1)
    have hy := affine_form_value gy ((-1:ℝ),1)
    norm_num [gx,gy,RationalAffineForm.value] at hx hy
    have hv := Value.add (Value.div (Value.const 1) hx (by norm_num))
      (Value.add (Value.div (Value.const 1) hy (by norm_num)) (Value.const 0))
    norm_num at hv
    simpa [affineReciprocalSum,gx,gy] using hv

theorem safe_but_presence_unknown : affineSegmentSafe [gx,gy] a b = true ∧
    classifyAffineWithSegment (fun _ => none) X Y [gx,gy] a b = .unknown := by
  constructor
  · decide +kernel
  · exact declining_unknown

def quadrant (x y : ℝ) : Prop := x < 0 ∧ 0 < y

theorem quadrant_path : ∀ t ∈ Set.Icc (0:ℝ) 1,
    quadrant (segment a.1 b.1 t) (segment a.2 b.2 t) := by
  intro t ht
  norm_num [quadrant,segment,a,b]
  constructor <;> nlinarith [ht.1,ht.2]

theorem restricted_presence : ∃ x y, X.Contains x ∧ Y.Contains y ∧
    quadrant x y ∧ Value x y (affineReciprocalSum [gx,gy]) 0 :=
  certifyAffineSegment_domain_sound exactBackend_sound quadrant_path (by decide +kernel)

theorem restricted_path_defined : ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ z,
    quadrant (segment a.1 b.1 t) (segment a.2 b.2 t) ∧
    Value (segment a.1 b.1 t) (segment a.2 b.2 t) (affineReciprocalSum [gx,gy]) z :=
  (affine_segment_domain_defined_iff [gx,gy] a b quadrant).mpr
    ⟨quadrant_path,by decide +kernel⟩

/-- Both endpoints are allowed, but every arithmetic zero is excluded. -/
def endpointsOnly (x y : ℝ) : Prop := (x = -1 ∧ y = 2) ∨ (x = -2 ∧ y = 1)

theorem endpoints_allowed : endpointsOnly a.1 a.2 ∧ endpointsOnly b.1 b.2 := by
  norm_num [endpointsOnly,a,b]

theorem endpoints_only_no_root : ¬ ∃ x y, endpointsOnly x y ∧
    Value x y (affineReciprocalSum [gx,gy]) 0 := by
  rintro ⟨x,y,hE,hv⟩
  have he := value_eq_realValue hv
  rcases hE with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    norm_num [affineReciprocalSum,Expr.realValue,RationalAffineForm.expression,gx,gy] at he

theorem endpoints_not_path : ¬ ∀ t ∈ Set.Icc (0:ℝ) 1,
    endpointsOnly (segment a.1 b.1 t) (segment a.2 b.2 t) := by
  intro h
  have hm := h (1/2) (by norm_num)
  norm_num [endpointsOnly,segment,a,b] at hm

/-- Restricting an empty box needs no assumption about the external domain. -/
theorem restricted_absence (E : ℝ → ℝ → Prop) :
    ¬ ∃ x y, (QInterval.point 1).Contains x ∧ (QInterval.point 1).Contains y ∧
      E x y ∧ Value x y (affineReciprocalSum [gx]) 0 := by
  apply classifyAffineWithSegment_domain_empty exactBackend_sound E (a := (1,1)) (b := (1,1))
  decide +kernel

end GeneralizedIntervalArithmetic.AffineSegmentChecks
#audit_namespace GeneralizedIntervalArithmetic.AffineSegmentChecks
