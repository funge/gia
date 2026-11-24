import PartialProperties
import AuditPolicy

namespace GeneralizedIntervalArithmetic.PartialPropertiesChecks
open PartialProperties DomainConstraints GeneralFamilyDemotion

noncomputable def ratio : PartialReal := fun x => if x = 0 then none else some (x/x)
def filled : PartialReal := fun _ => some 1

theorem removable_extension : Extends ratio filled := by
  intro x z hz
  unfold ratio at hz
  split_ifs at hz with hx
  have he : z = 1 := by simpa [div_self hx,eq_comm] using hz
  simp [filled,he]

theorem extension_is_continuous : ContinuousOnPartial filled Set.univ :=
  ⟨fun _ => 1,continuousOn_const,fun _ _ => rfl⟩

theorem original_hole_is_not_filled : ratio 0 = none ∧ ratio 0 ≠ some 1 := by
  simp [ratio]

theorem original_not_defined_continuous_on_univ : ¬ ContinuousOnPartial ratio Set.univ := by
  rintro ⟨g,_,h⟩
  have hh := h 0 (Set.mem_univ 0)
  simp [ratio] at hh

theorem strict_composition_preserves_hole : compose filled ratio 0 = none := by
  simp [compose,ratio]

theorem defined_composition_control : compose filled ratio 2 = some 1 := by
  norm_num [compose,ratio,filled]

theorem filled_model : Sound (fun _ : ℝ => Set.singleton 1)
    (exactDomain (fun _ => True)) (fun _ (_ : Unit) => True)
    (fun p (_ : Unit) z => filled p = some z) := by
  intro p w _
  refine ⟨?_,fun _ => ⟨1,rfl⟩,fun _ => trivial⟩
  intro z hz
  simpa [filled,eq_comm] using hz

theorem original_bounds_from_extension : Sound (fun _ : ℝ => Set.singleton 1)
    (exactInputDomain (fun _ (_ : Unit) => True)
      (fun p (_ : Unit) z => ratio p = some z))
    (fun _ (_ : Unit) => True) (fun p (_ : Unit) z => ratio p = some z) :=
  extension_bounds_original ratio filled removable_extension (fun p (_ : Unit) => p)
    _ _ _ filled_model

theorem original_domain_stays_false_at_hole :
    ¬ (exactInputDomain (fun _ (_ : Unit) => True)
      (fun p (_ : Unit) z => ratio p = some z)).possible 0 := by
  simp [exactInputDomain,ratio]

theorem cannot_copy_extended_totality : ¬ Sound (fun _ : ℝ => Set.singleton 1)
    (exactDomain (fun _ => True)) (fun _ (_ : Unit) => True)
    (fun p (_ : Unit) z => ratio p = some z) := by
  intro h
  obtain ⟨z,hz⟩ := (h 0 () trivial).2.1 trivial
  simp [ratio] at hz

theorem property_flag_requires_evidence :
    ¬ Tracks (exactDomain (fun _ : Unit => True))
      (fun _ (_ : Unit) => True) (fun _ _ => False) := by
  intro h
  exact (h () () trivial).1 trivial

theorem compose_continuous_control : ContinuousOnPartial (compose filled filled) Set.univ :=
  continuous_compose extension_is_continuous extension_is_continuous (fun _ _ _ _ => Set.mem_univ _)

theorem restricted_continuous_control :
    ContinuousOnPartial (restrict filled (Set.Icc (0:ℝ) 1)) (Set.Icc (0:ℝ) 1) :=
  continuous_restrict extension_is_continuous (Set.subset_univ _)

end GeneralizedIntervalArithmetic.PartialPropertiesChecks
#audit_namespace GeneralizedIntervalArithmetic.PartialPropertiesChecks
