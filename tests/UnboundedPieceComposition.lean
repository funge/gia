import UnboundedPieceComposition
import AuditPolicy
namespace GeneralizedIntervalArithmetic.UnboundedPieceCompositionChecks
open FiniteGuardPieces GuardedPieceComposition UnboundedPieceComposition

/-- Printed §2.13.1 reciprocal example, restricted to actual real members. -/
theorem source_reciprocal_image (z : ℝ) :
    (∃ x : ℝ, -1 ≤ x ∧ x ≤ 1 ∧ x ≠ 0 ∧ z=1/x) ↔ z≤-1 ∨ 1≤z := by
  simpa using (SplitQuotient.reciprocal_image (l:=(-1:ℝ)) (u:=1) (z:=z)
    (by norm_num) (by norm_num))

def d : QAffine := ⟨-1/2,1/2⟩
def s : QAffine := ⟨0,1⟩
def code : List Piece := shift s (reciprocalCode unitGuard d (-1/2) (1/2)).compile

theorem d_value (t : ℝ) : d.value t = t-1/2 := by norm_num [d,QAffine.value]; ring
theorem s_value (t : ℝ) : s.value t = t := by simp [s,QAffine.value]
theorem bounds (t : ℝ) (ht : guardHolds unitGuard t) :
    (-1/2:ℝ) ≤ d.value t ∧ d.value t ≤ (1/2:ℝ) := by
  have h := (unit_guard_exact t).1 ht
  rw [d_value]; constructor <;> linarith [h.1,h.2]

def actual (t z : ℝ) : Prop := ∃ v, AffinePoleSplit.Values unitGuard d t v ∧ z=v+s.value t

theorem enclosed {t z : ℝ} (h : actual t z) : z ∈ pieces code t :=
  composed_encloses (by intro t ht; simpa using bounds t ht) h

theorem domain_exact (t : ℝ) : (pieces code t).Nonempty ↔ ∃ z, actual t z := by
  exact composed_domain s unitGuard d (-1/2) (1/2) t

theorem semantic_expression (t z : ℝ) : actual t z ↔
    guardHolds unitGuard t ∧ Value (d.value t) (s.value t)
      (.add (.div (.const 1) .x) .y) z := composed_expression unitGuard d s t z

theorem code_exact (t z : ℝ) : z ∈ pieces code t ↔
    (t∈Set.Icc (0:ℝ) 1 ∧ t<1/2 ∧ z-t ≤ -2) ∨
    (t∈Set.Icc (0:ℝ) 1 ∧ 1/2<t ∧ 2 ≤ z-t) := by
  rw [code,shift_exact,reciprocal_code_exact,unit_guard_exact,d_value,s_value]
  norm_num

theorem central_window_excluded (t z : ℝ) (hz : z∈Set.Icc (-1:ℝ) 1) :
    z ∉ pieces code t := by
  intro h
  rcases (code_exact t z).1 h with ⟨_,ht,hv⟩ | ⟨_,ht,hv⟩ <;> linarith [hz.1,hz.2]

theorem hole_empty : pieces code (1/2:ℝ) = ∅ := by
  ext z; simp [code_exact]

theorem left_actual : actual 0 (-2) := by
  refine ⟨-2,⟨(unit_guard_exact _).2 (by norm_num),?_,?_⟩,?_⟩ <;>
    norm_num [d_value,s_value]
theorem right_actual : actual 1 3 := by
  refine ⟨2,⟨(unit_guard_exact _).2 (by norm_num),?_,?_⟩,?_⟩ <;>
    norm_num [d_value,s_value]

/-- A convex projected hull admits zero although every guarded output excludes it. -/
theorem projected_hull_fills_gap :
    (0:ℝ) ∈ ExtendedImageHull.hull {z | ∃ t, actual t z} := by
  have hl := ExtendedImageHull.sound {z | ∃ t, actual t z} (show (-2:ℝ) ∈ _ from ⟨0,left_actual⟩)
  have hu := ExtendedImageHull.sound {z | ∃ t, actual t z} (show (3:ℝ) ∈ _ from ⟨1,right_actual⟩)
  exact ⟨hl.1.trans (EReal.coe_le_coe_iff.mpr (by norm_num)),
    (EReal.coe_le_coe_iff.mpr (by norm_num : (0:ℝ) ≤ 3)).trans hu.2⟩

/-- Pointwise enclosure is NOT an exact expression value. -/
theorem admitted_but_not_attained :
    (-7/4:ℝ) ∈ pieces code (1/4) ∧ ¬ actual (1/4) (-7/4) := by
  constructor
  · rw [code_exact]; norm_num
  · rintro ⟨v,⟨_,_,hv⟩,hz⟩
    norm_num [d_value] at hv
    norm_num [s_value,hv] at hz

theorem ray_unbounded (l : ℝ) : ∃ z, z ∈ pieces code (1/4) ∧ z<l := by
  refine ⟨min (-2) (l-1),?_,?_⟩
  · rw [code_exact]
    left
    refine ⟨by norm_num,by norm_num,?_⟩
    linarith [min_le_left (-2:ℝ) (l-1)]
  · linarith [min_le_right (-2:ℝ) (l-1)]

theorem no_exceptional_members :
    let H := TaggedConversion.lift ExtendedImageHull.hull
      (ExceptionalComparisons.Value.finite '' pieces code (1/4))
    ExceptionalComparisons.Value.posInf ∉ H ∧ ExceptionalComparisons.Value.negInf ∉ H ∧
      ExceptionalComparisons.Value.undefined ∉ H := finite_tags_only _

theorem rational_left : test code 0 (-2) = true := by decide +kernel
theorem rational_right : test code 1 3 = true := by decide +kernel
theorem rational_actual : test code (1/4) (-15/4) = true := by decide +kernel
theorem rational_gap : test code (1/4) 0 = false := by decide +kernel
theorem rational_pole : test code (1/2) 100 = false := by decide +kernel
theorem rational_outside : test code 2 100 = false := by decide +kernel

def openRay : List Piece := [[upper ⟨0,0⟩ true]]
theorem open_tip_excluded : test (shift s openRay) (1/4) (1/4) = false := by decide +kernel
theorem open_inside : test (shift s openRay) (1/4) 0 = true := by decide +kernel
theorem empty_preserved (t : ℝ) : pieces (shift s []) t = ∅ := by
  simp [shift,pieces,IntervalSetDenotation.denote]

#eval [(0,-2),(1,3),(1/4,-15/4),(1/4,0),(1/2,100),(2,100)].map
  (fun (t,z) => test code t z)
#audit_namespace GeneralizedIntervalArithmetic.UnboundedPieceCompositionChecks
end GeneralizedIntervalArithmetic.UnboundedPieceCompositionChecks
