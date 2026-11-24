import GeneralFamilyDemotion
import AuditPolicy

namespace GeneralizedIntervalArithmetic.GeneralFamilyDemotionChecks
open GeneralFamilyDemotion DomainConstraints

def seed : LinearInterval := .exact ⟨0,1⟩
def unitDomain : DomainBounds ℝ := exactDomain (fun t => t ∈ Set.Icc (0:ℝ) 1)
def seedRel (t : ℝ) (_ : Unit) (z : ℝ) : Prop := t ∈ Set.Icc (0:ℝ) 1 ∧ z = t

theorem seed_sound : Sound (fun t => {z | seed.Contains t z}) unitDomain
    (fun _ (_ : Unit) => True) seedRel := by
  intro t w _
  refine ⟨?_,?_,?_⟩
  · intro z hz
    simpa [seed,QAffine.value,hz.2] using
      (linear_exact_contains (QAffine.mk 0 1) t t).mpr (by simp [QAffine.value])
  · intro ht
    exact ⟨t,ht,rfl⟩
  · rintro ⟨z,ht,_⟩
    exact ht

theorem projected_sound : Sound (fun _ => {z | seed.hull.Contains z}) unitDomain
    (fun _ (_ : Unit) => True) seedRel :=
  affine_constant_sound seed _ _ seed_sound

theorem strict_correlation_loss :
    (seed.sub seed).Contains (1/2) 0 ∧
    ¬ (seed.sub seed).Contains (1/2) 1 ∧
    (seed.hull.sub seed.hull).Contains 1 := by
  constructor
  · exact (linear_exact_cancel ⟨0,1⟩ _ _).mpr rfl
  constructor
  · rw [show (seed.sub seed).Contains (1/2) 1 ↔ (1:ℝ)=0 from linear_exact_cancel ⟨0,1⟩ _ _]
    norm_num
  · norm_num [seed,LinearInterval.hull,LinearInterval.exact,QInterval.sub,QInterval.Contains]

theorem projected_hole_sound : Sound (fun _ => {z | seed.hull.Contains z})
    ((exactDomain (fun t => t ≠ (1/2:ℝ))).inter unitDomain)
    (fun _ (_ : Unit) => True) (fun t w z => t ≠ (1/2:ℝ) ∧ seedRel t w z) :=
  GeneralFamilyDemotion.restrict_sound projected_sound _

theorem hole_stays_impossible :
    ¬ (((exactDomain (fun t => t ≠ (1/2:ℝ))).inter unitDomain).possible (1/2)) := by
  simp [DomainBounds.inter,exactDomain]

/-- Same parameter, two admitted inputs; only one input has a defined value. -/
def mixed (_ : Unit) (w : Bool) (z : ℝ) : Prop := w = true ∧ z = 0

theorem mixed_domain_not_total :
    (exactInputDomain (fun _ (_ : Bool) => True) mixed).possible () ∧
    ¬ (exactInputDomain (fun _ (_ : Bool) => True) mixed).definite () := by
  constructor
  · exact ⟨true,0,trivial,rfl,rfl⟩
  · intro h
    obtain ⟨z,hz⟩ := h.2 false trivial
    simp [mixed] at hz

theorem mixed_hull_sound : Sound
    (fun p => ExtendedImageHull.hull (outputs (fun _ (_ : Bool) => True) mixed p))
    (exactInputDomain (fun _ (_ : Bool) => True) mixed)
    (fun _ (_ : Bool) => True) mixed := exact_hull_sound _ _

/-- Keeping the numeric set but strengthening the domain can destroy soundness. -/
theorem false_totality_is_unsound : ¬ Sound (fun _ : Unit => Set.univ)
    (exactDomain (fun _ => True)) (fun _ (_ : Bool) => True) mixed := by
  intro h
  obtain ⟨z,hz⟩ := (h () false trivial).2.1 trivial
  simp [mixed] at hz

theorem empty_input_guard :
    ¬ (exactInputDomain (fun _ : Unit => fun _ : Unit => False)
      (fun _ _ z => z = (0:ℝ))).definite () ∧
    ¬ (exactInputDomain (fun _ : Unit => fun _ : Unit => False)
      (fun _ _ z => z = (0:ℝ))).possible () := by
  simp [exactInputDomain]

/-- If the source rules out all defined values, arbitrary numeric payloads are
allowed; no value can be inferred from that payload. -/
theorem nowhere_defined_arbitrary_payload :
    Demotes (fun _ : Unit => Set.univ) (exactDomain (fun _ => False))
      (fun _ => ∅) (exactDomain (fun _ => False)) := by
  exact ⟨fun _ => ⟨id,id⟩,fun _ h => False.elim h⟩

end GeneralizedIntervalArithmetic.GeneralFamilyDemotionChecks
#audit_namespace GeneralizedIntervalArithmetic.GeneralFamilyDemotionChecks
