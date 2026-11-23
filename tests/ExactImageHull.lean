import ExactImageHull
import AuditPolicy

namespace GeneralizedIntervalArithmetic.ExactImageHullChecks
open ExactImageHull

/-- The least closed hull can have unattainable endpoints. -/
theorem open_hull : hull (Set.Ioo (0:ℝ) 1) = Set.Icc 0 1 := by
  simp only [hull,csInf_Ioo (by norm_num : (0:ℝ)<1),csSup_Ioo (by norm_num : (0:ℝ)<1)]

theorem open_nonattainment :
    (0:ℝ) ∈ hull (Set.Ioo 0 1) ∧ (1:ℝ) ∈ hull (Set.Ioo 0 1) ∧
    (0:ℝ) ∉ Set.Ioo (0:ℝ) 1 ∧ (1:ℝ) ∉ Set.Ioo (0:ℝ) 1 := by
  rw [open_hull]; norm_num

theorem disconnected_hull : hull ({0,2} : Set ℝ) = Set.Icc 0 2 := by
  apply eq_of_attained
  · intro z hz; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> norm_num
  · simp
  · simp

theorem hull_membership_is_not_attainment :
    (1:ℝ) ∈ hull ({0,2}:Set ℝ) ∧ (1:ℝ) ∉ ({0,2}:Set ℝ) := by
  rw [disconnected_hull]; norm_num

theorem singleton_hull (a : ℝ) : hull {a} = Set.Icc a a := by
  apply eq_of_attained
  · intro z hz; simp only [Set.mem_singleton_iff] at hz; subst z; exact ⟨le_rfl,le_rfl⟩
  · simp
  · simp

theorem refinement_control : hull ({0}:Set ℝ) ⊆ hull ({0,2}:Set ℝ) := by
  apply mono (by simp) (show BddBelow ({0,2}:Set ℝ) from ⟨0,by intro x hx; simp at hx; rcases hx with rfl | rfl <;> norm_num⟩)
    (show BddAbove ({0,2}:Set ℝ) from ⟨2,by intro x hx; simp at hx; rcases hx with rfl | rfl <;> norm_num⟩)
  intro z hz; simp only [Set.mem_singleton_iff] at hz; subst z; simp

def unit : QInterval := ⟨0,1,by norm_num⟩
def negUnit : QInterval := ⟨-1,0,by norm_num⟩
def zero : QInterval := ⟨0,0,le_rfl⟩

theorem independent_sum : hull (sums unit negUnit) = Set.Icc (-1) 1 := by
  rw [add_exact]; ext z; norm_num [unit,negUnit,zero,QInterval.add,QInterval.Contains]

theorem attained_sum_endpoints : (-1:ℝ) ∈ sums unit negUnit ∧ (1:ℝ) ∈ sums unit negUnit := by
  simpa [unit,negUnit,QInterval.add] using sums_endpoints unit negUnit

/-- Same t is retained in both summands, rather than replaced by independent inputs. -/
theorem paired_values : values (Set.Icc (0:ℝ) 1) (fun t z => z = t + (-t)) = {0} := by
  ext z
  constructor
  · rintro ⟨t,ht,hz⟩; simpa using hz
  · intro hz; simp only [Set.mem_singleton_iff] at hz; subst z
    exact ⟨0,by norm_num,by norm_num⟩

theorem paired_vs_independent :
    hull (values (Set.Icc (0:ℝ) 1) (fun t z => z = t + (-t))) = Set.Icc 0 0 ∧
    (1:ℝ) ∈ hull (sums unit negUnit) ∧
    (1:ℝ) ∉ hull (values (Set.Icc (0:ℝ) 1) (fun t z => z = t + (-t))) := by
  rw [paired_values,singleton_hull,independent_sum]; norm_num

/-- A pole is not assigned a value by the image constructor. -/
theorem partial_values :
    values ({0,1}:Set ℝ) (fun t z => t ≠ 0 ∧ z = 1/t) = {1} := by
  ext z
  constructor
  · rintro ⟨t,ht,hne,hz⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact (hne rfl).elim
    · simpa using hz
  · intro hz; simp only [Set.mem_singleton_iff] at hz; subst z
    exact ⟨1,by simp,by norm_num,by norm_num⟩

theorem no_value_at_pole : ¬ ∃ z, (0:ℝ) ≠ 0 ∧ z = 1/(0:ℝ) := by simp

theorem zero_sum_hull : hull (sums zero zero) = Set.Icc 0 0 := by
  rw [add_exact]; ext z
  norm_num [zero,QInterval.add,QInterval.Contains]
  exact ⟨fun h => le_antisymm h.2 h.1,fun h => by simp [h]⟩

theorem empty_not_eligible : ¬ (∅ : Set ℝ).Nonempty := by simp

theorem loose_rounding :
    hull (sums unit unit) ⊆ {z | (roundedAdd unit unit (fun q => q-1) (fun q => q+1)
      (by norm_num [unit]) (by norm_num [unit])).Contains z} :=
  rounded_add_contains_hull unit unit _ _ _ _

theorem outward_is_not_exact :
    (roundedAdd unit unit (fun q => q-1) (fun q => q+1)
      (by norm_num [unit]) (by norm_num [unit])).Contains (-1) ∧
    (-1:ℝ) ∉ hull (sums unit unit) := by
  rw [add_exact]; norm_num [roundedAdd,unit,QInterval.add,QInterval.Contains]

/-- Real-valued observations instantiate the existing contract; not a native test. -/
theorem observed_addition : ∀ z ∈ hull (sums unit unit),
    HardwareAddition.Contains some (⟨-1,3⟩ : HardwareAddition.Bounds ℝ) z := by
  apply hardware_add_contains_hull (decode := some)
    (A := ⟨0,1⟩) (B := ⟨0,1⟩) unit unit
    (lower := some (-1,0)) (upper := some (2,3))
  all_goals norm_num [unit,HardwareAddition.CallSound,HardwareAddition.assemble]

theorem failed_observation :
    HardwareAddition.assemble (none : Option (ℝ × ℝ)) (some (2,2)) = none := rfl

#audit_namespace GeneralizedIntervalArithmetic.ExactImageHullChecks
end GeneralizedIntervalArithmetic.ExactImageHullChecks
