import AffinePoleSplit
import AuditPolicy
namespace GeneralizedIntervalArithmetic.AffinePoleSplitChecks
open FiniteGuardPieces GuardedPieceComposition AffinePoleSplit

def d : QAffine := ⟨-1/2,1/2⟩
def g : Guard := unitGuard

theorem denominator (t : ℝ) : d.value t = t-1/2 := by
  norm_num [d,QAffine.value]; ring

theorem exact_rays (z : ℝ) :
    (∃ t, Values g d t z) ↔ z ≤ -2 ∨ 2 ≤ z := by
  have hr := SplitQuotient.reciprocal_image (z:=z)
    (l:=(-1/2:ℝ)) (u:=(1/2:ℝ)) (by norm_num) (by norm_num)
  norm_num at hr
  rw [←hr]
  constructor
  · rintro ⟨t,hg,hn,hz⟩
    have ht := (unit_guard_exact t).1 hg
    rw [denominator] at hn hz
    exact ⟨t-1/2,by linarith [ht.1],by linarith [ht.2],hn,by simpa using hz⟩
  · rintro ⟨x,hl,hu,hn,hz⟩
    refine ⟨x+1/2,?_,?_,?_⟩
    · exact (unit_guard_exact _).2 ⟨by linarith,by linarith⟩
    · simpa [denominator] using hn
    · simpa [denominator] using hz

theorem unbounded_above (u : ℝ) : ∃ t z, Values g d t z ∧ u < z := by
  have hz : 2 ≤ max 2 (u+1) := le_max_left _ _
  obtain ⟨t,ht⟩ := (exact_rays _).2 (Or.inr hz)
  exact ⟨t,_,ht,by linarith [le_max_right (2:ℝ) (u+1)]⟩

theorem unbounded_below (l : ℝ) : ∃ t z, Values g d t z ∧ z < l := by
  obtain ⟨t,ht⟩ := (exact_rays (min (-2) (l-1))).2 (Or.inl (min_le_left _ _))
  exact ⟨t,_,ht,by linarith [min_le_right (-2:ℝ) (l-1)]⟩

theorem left_tip : Values g d 0 (-2) := by
  refine ⟨(unit_guard_exact _).2 (by norm_num),?_,?_⟩ <;> norm_num [denominator]
theorem right_tip : Values g d 1 2 := by
  refine ⟨(unit_guard_exact _).2 (by norm_num),?_,?_⟩ <;> norm_num [denominator]
theorem pole_recorded : guardHolds (zero g d) (1/2:ℝ) := by
  rw [zero_exact]; exact ⟨(unit_guard_exact _).2 (by norm_num),by norm_num [denominator]⟩
theorem pole_absent : ¬∃ z, Values g d (1/2:ℝ) z := zero_absent pole_recorded

def reciprocal : Expr := .div (.const 1) .x
theorem whole_hull_fails :
    (evalGuarded (.exact d) (.exact ⟨1,1⟩) reciprocal).isNone = true := by decide +kernel

theorem negative_endpoint : AffinePoleSplit.admitted? g d 0 = true := by decide +kernel
theorem positive_endpoint : AffinePoleSplit.admitted? g d 1 = true := by decide +kernel
theorem zero_rejected : AffinePoleSplit.admitted? g d (1/2) = false := by decide +kernel
theorem outside_rejected : AffinePoleSplit.admitted? g d 2 = false := by decide +kernel

def openGuard : Guard := [(⟨0,-1⟩,true),(⟨-1,0⟩,true)]
theorem open_left : AffinePoleSplit.admitted? openGuard d 0 = false := by decide +kernel
theorem open_right : AffinePoleSplit.admitted? openGuard d 1 = false := by decide +kernel
theorem open_interior : AffinePoleSplit.admitted? openGuard d (1/4) = true := by decide +kernel
theorem constant_zero : AffinePoleSplit.admitted? g ⟨0,0⟩ (1/4) = false := by decide +kernel
theorem constant_positive : AffinePoleSplit.admitted? g ⟨1,1⟩ (1/4) = true := by decide +kernel
theorem constant_negative : AffinePoleSplit.admitted? g ⟨-1,-1⟩ (1/4) = true := by decide +kernel

/-- A denominator value from another parameter cannot repair the pole. -/
theorem separate_witness_wrong :
    (∃ t, guardHolds g t ∧ d.value t ≠ 0) ∧ ¬∃ z, Values g d (1/2:ℝ) z := by
  exact ⟨⟨0,(unit_guard_exact _).2 (by norm_num),by norm_num [denominator]⟩,pole_absent⟩

#eval [0,1/4,1/2,3/4,1,2].map (AffinePoleSplit.admitted? g d)
#audit_namespace GeneralizedIntervalArithmetic.AffinePoleSplitChecks
end GeneralizedIntervalArithmetic.AffinePoleSplitChecks
