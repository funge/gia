import IntervalSetDenotation
import AuditPolicy
namespace GeneralizedIntervalArithmetic.IntervalSetDenotationChecks
open IntervalSetDenotation

def pieces (b : Bool) (_ : Unit) : Set ℝ := if b then {1} else {-1}
theorem two_pieces_exact : denote pieces Set.univ () = ({-1,1} : Set ℝ) := by
  ext z
  simp [denote,pieces,Bool.exists_bool,or_comm]

theorem disconnected_strict :
    (0:ℝ) ∈ ExtendedImageHull.hull (denote pieces Set.univ ()) ∧
    (0:ℝ) ∉ denote pieces Set.univ () := by
  rw [two_pieces_exact]
  constructor
  · have hl := (ExtendedImageHull.sound ({-1,1} : Set ℝ) (by norm_num : (-1:ℝ) ∈ ({-1,1} : Set ℝ))).1
    have hu := (ExtendedImageHull.sound ({-1,1} : Set ℝ) (by norm_num : (1:ℝ) ∈ ({-1,1} : Set ℝ))).2
    exact ⟨hl.trans (EReal.coe_le_coe_iff.mpr (by norm_num)), (EReal.coe_le_coe_iff.mpr (by norm_num : (0:ℝ) ≤ 1)).trans hu⟩
  · norm_num

theorem identifiers_are_not_values :
    denote (fun _ : Bool => fun _ : Unit => ({0}:Set ℝ)) ({false} ∩ {true}) () = ∅ ∧
    denote (fun _ : Bool => fun _ : Unit => ({0}:Set ℝ)) {false} () ∩
      denote (fun _ : Bool => fun _ : Unit => ({0}:Set ℝ)) {true} () = {0} := by
  constructor <;> ext z <;> simp [denote]

theorem touching_closed : Set.Icc (0:ℝ) 1 ∩ Set.Icc 1 2 = {1} := by
  ext x
  simp only [Set.mem_inter_iff,Set.mem_Icc,Set.mem_singleton_iff]
  constructor
  · intro h; linarith [h.1.2,h.2.1]
  · rintro rfl; norm_num

theorem touching_open : Set.Ioo (0:ℝ) 1 ∩ Set.Ioo 1 2 = ∅ := by
  ext x
  simp only [Set.mem_inter_iff,Set.mem_Ioo,Set.mem_empty_iff_false,iff_false]
  intro h; linarith [h.1.2,h.2.1]

theorem retained_hole :
    denote (point (fun x : ℝ => if x = 0 then none else some (1/x))) Set.univ 0 = ∅ := by
  apply absent_points
  simp

theorem same_parameter :
    denote (point (fun x : ℝ => some x)) Set.univ 2 = {2} := by
  rw [points_exact]; ext z; simp [eq_comm]

theorem no_finite_exactness_claim :
    denote (fun r : ℝ => fun _ : Unit => ({r}:Set ℝ)) (Set.Ioo 0 1) () = Set.Ioo 0 1 := by
  ext z; simp [denote]

theorem equal_bounds_singleton : ExtendedImageHull.interval (2:EReal) 2 = ({2}:Set ℝ) :=
  equal_real_bounds 2
end GeneralizedIntervalArithmetic.IntervalSetDenotationChecks
#audit_namespace GeneralizedIntervalArithmetic.IntervalSetDenotationChecks
