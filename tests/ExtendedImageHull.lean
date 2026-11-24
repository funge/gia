import ExtendedImageHull
import AuditPolicy

namespace GeneralizedIntervalArithmetic.ExtendedImageHullChecks
open ExtendedImageHull

theorem empty_control : lower ∅ = ⊤ ∧ upper ∅ = ⊥ ∧ hull ∅ = ∅ :=
  ⟨empty_bounds.1,empty_bounds.2,empty_hull⟩

theorem empty_refinement (S : Set ℝ) : hull ∅ ⊆ hull S := mono (Set.empty_subset _)

theorem univ_bounds : lower Set.univ = ⊥ ∧ upper Set.univ = ⊤ := by
  constructor
  · apply lower_unbounded
    rintro ⟨l,hl⟩
    have h := hl (show l-1 ∈ (Set.univ : Set ℝ) from Set.mem_univ _)
    linarith
  · apply upper_unbounded
    rintro ⟨u,hu⟩
    have h := hu (show u+1 ∈ (Set.univ : Set ℝ) from Set.mem_univ _)
    linarith

theorem univ_hull : hull Set.univ = Set.univ := by
  ext x
  simp [hull,interval,univ_bounds.1,univ_bounds.2]

theorem right_ray_bounds : lower (Set.Ici (0:ℝ)) = 0 ∧ upper (Set.Ici (0:ℝ)) = ⊤ := by
  constructor
  · rw [lower_finite (S := Set.Ici (0:ℝ)) (by exact ⟨0,by simp⟩) ⟨0,fun _ h => h⟩,csInf_Ici]
    rfl
  · apply upper_unbounded
    rintro ⟨u,hu⟩
    have hm : 0 ≤ max u 0 := le_max_right _ _
    have hm' : u ≤ max u 0 := le_max_left _ _
    have h := hu (show max u 0 + 1 ∈ Set.Ici (0:ℝ) by simp only [Set.mem_Ici]; linarith)
    linarith

theorem left_ray_bounds : lower (Set.Iic (0:ℝ)) = ⊥ ∧ upper (Set.Iic (0:ℝ)) = 0 := by
  constructor
  · apply lower_unbounded
    rintro ⟨l,hl⟩
    have hm : min l 0 ≤ 0 := min_le_right _ _
    have hm' : min l 0 ≤ l := min_le_left _ _
    have h := hl (show min l 0 - 1 ∈ Set.Iic (0:ℝ) by simp only [Set.mem_Iic]; linarith)
    linarith
  · rw [upper_finite (S := Set.Iic (0:ℝ)) (by exact ⟨0,by simp⟩) ⟨0,fun _ h => h⟩,csSup_Iic]
    rfl

theorem ray_membership : hull (Set.Ici (0:ℝ)) = Set.Ici 0 ∧
    hull (Set.Iic (0:ℝ)) = Set.Iic 0 := by
  constructor <;> ext x <;>
    simp [hull,interval,right_ray_bounds.1,right_ray_bounds.2,left_ray_bounds.1,left_ray_bounds.2]

theorem bounded_closed : hull (Set.Icc (-2:ℝ) 3) = Set.Icc (-2) 3 := by
  have h := interval_fixed ((-2:ℝ):EReal) ((3:ℝ):EReal)
  simpa [interval] using h

theorem open_agreement : hull (Set.Ioo (0:ℝ) 1) = Set.Icc 0 1 := by
  rw [finite_agreement (by exact ⟨1/2,by norm_num⟩)
    ⟨0,fun _ h => h.1.le⟩ ⟨1,fun _ h => h.2.le⟩]
  simp [ExactImageHull.hull,csInf_Ioo (by norm_num : (0:ℝ)<1),csSup_Ioo (by norm_num : (0:ℝ)<1)]

theorem open_nonattainment : (0:ℝ) ∈ hull (Set.Ioo 0 1) ∧
    (0:ℝ) ∉ Set.Ioo (0:ℝ) 1 := by rw [open_agreement]; norm_num

theorem empty_has_no_real_witness : ¬ ∃ x : ℝ, lower ∅ ≤ x ∧ (x:EReal) ≤ upper ∅ := by
  simp [empty_bounds.1,empty_bounds.2]

/-- Even equal infinite bounds need not have any REAL member. -/
theorem top_singleton_has_no_real_output : interval ⊤ ⊤ = ∅ := by
  ext x
  simp [interval]

theorem pole_image_empty : hull {z : ℝ | ∃ t ∈ ({0}:Set ℝ), t ≠ 0 ∧ z = 1/t} = ∅ := by
  have h : {z : ℝ | ∃ t ∈ ({0}:Set ℝ), t ≠ 0 ∧ z = 1/t} = ∅ := by ext z; simp
  rw [h,empty_hull]

theorem shared_input_control :
    hull {z : ℝ | ∃ t ∈ Set.univ, z = t + (-t)} = {0} := by
  have h : {z : ℝ | ∃ t ∈ Set.univ, z = t + (-t)} = {0} := by ext z; simp
  rw [h]
  have hi := interval_fixed ((0:ℝ):EReal) ((0:ℝ):EReal)
  have he : interval ((0:ℝ):EReal) ((0:ℝ):EReal) = ({0}:Set ℝ) := by
    ext x
    simp [interval, ← le_antisymm_iff, eq_comm]
  simpa only [he] using hi

theorem partial_relation_client :
    hull {z : ℝ | ∃ t ∈ Set.Ici (1:ℝ), t ≠ 0 ∧ z = 1/t} ⊆ interval 0 1 := by
  apply relation_enclosure
  intro t ht z hz
  rcases hz with ⟨_,rfl⟩
  have ht' : (0:ℝ) < t := lt_of_lt_of_le (by norm_num) ht
  have hlo : (0:ℝ) ≤ 1/t := le_of_lt (one_div_pos.mpr ht')
  have hhi : (1:ℝ)/t ≤ 1 := (div_le_one ht').mpr ht
  exact ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩

theorem empty_finite_hull_is_not_applicable :
    (0:ℝ) ∈ ExactImageHull.hull ∅ ∧ (0:ℝ) ∉ hull ∅ := by
  simp [ExactImageHull.hull,empty_hull]

end GeneralizedIntervalArithmetic.ExtendedImageHullChecks
#audit_namespace GeneralizedIntervalArithmetic.ExtendedImageHullChecks
