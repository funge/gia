import DomainConstraints
import AuditPolicy

namespace GeneralizedIntervalArithmetic.DomainConstraintsChecks
open DomainConstraints StrictComparison

def unknownD {α : Type*} : DomainBounds α := ⟨fun _ => False, fun _ => True, by simp⟩

theorem empty_constraints_true (p : ℚ) :
    description (allDomains ([] : List (DomainBounds ℚ))) p = .trueOnly := by
  simp [description, allDomains, exactDomain]

theorem unknown_does_not_assert_exists :
    (unknownD : DomainBounds Unit).Compatible () False ∧
    description (unknownD : DomainBounds Unit) () = .both := by
  simp [DomainBounds.Compatible, unknownD, description]

/-- Each constraint has a satisfying parameter, but not the SAME parameter. -/
def yesD : DomainBounds Bool := exactDomain (fun p => p = true)
def noD : DomainBounds Bool := exactDomain (fun p => p = false)

theorem separate_parameters_do_not_combine :
    (∃ p, yesD.possible p) ∧ (∃ p, noD.possible p) ∧
    ¬ ∃ p, (allDomains [yesD, noD]).possible p := by
  simp [all_possible, yesD, noD, exactDomain]

theorem incompatible_same_parameter (p : Bool) :
    description (allDomains [yesD, noD]) p = .falseOnly := by
  cases p <;> simp [description, allDomains, yesD, noD, exactDomain, DomainBounds.inter]

def closedLeft : DomainBounds ℚ := exactDomain (fun t => 0 ≤ t)
def closedRight : DomainBounds ℚ := exactDomain (fun t => t ≤ 0)

theorem shared_boundary_retained :
    description (allDomains [closedLeft, closedRight]) 0 = .trueOnly ∧
    description (allDomains [closedLeft, closedRight]) 1 = .falseOnly := by
  norm_num [description, allDomains, closedLeft, closedRight, exactDomain, DomainBounds.inter]

def unitD : DomainBounds ℚ := exactDomain (fun t => 0 ≤ t ∧ t ≤ 1)
def holeD : DomainBounds ℚ := exactDomain (fun t => t ≠ 1/2)

theorem hole_and_endpoints :
    description (allDomains [unitD, holeD]) 0 = .trueOnly ∧
    description (allDomains [unitD, holeD]) 1 = .trueOnly ∧
    description (allDomains [unitD, holeD]) (1/2) = .falseOnly := by
  norm_num [description, allDomains, unitD, holeD, exactDomain, DomainBounds.inter]

theorem exact_to_unknown {α : Type*} (P : α → Prop) :
    Refines (exactDomain P) unknownD := by
  intro p; simp [exactDomain, unknownD]

theorem weakened_family : Refines (allDomains [yesD, noD])
    (allDomains [unknownD, unknownD]) := by
  exact all_refines [true, false] (fun b => if b then yesD else noD)
    (fun _ => unknownD) (by intro b _; cases b <;> exact exact_to_unknown _)

theorem weakening_loses_information (p : Bool) :
    (description (allDomains [yesD, noD]) p).Refines
      (description (allDomains [unknownD, unknownD]) p) :=
  refines_description weakened_family p

def poleGuard : DomainBounds ℚ := exactDomain (fun t => t ≠ 0)

theorem partial_guard_at_same_parameter (p : ℚ) :
    (allDomains [poleGuard, unitD]).Compatible p (p ≠ 0 ∧ 0 ≤ p ∧ p ≤ 1) := by
  simpa using partial_guard_compatible [()] (fun _ => unitD)
    (fun _ => 0 ≤ p ∧ p ≤ 1) poleGuard (p ≠ 0) p
    (fun _ _ => ⟨id, id⟩) ⟨id, id⟩

def xForm : RationalAffineForm := ⟨1, 0, 0⟩

theorem reciprocal_existing_semantics (p : ℝ × ℝ) :
    (allDomains [exactDomain (fun q => xForm.value q ≠ 0)]).Compatible p
      (∃ z, Value p.1 p.2 (affineReciprocalSum [xForm]) z) :=
  reciprocal_constraints [xForm] p

theorem reciprocal_defined_and_pole :
    (∃ z, Value 1 0 (affineReciprocalSum [xForm]) z) ∧
    ¬ ∃ z, Value 0 0 (affineReciprocalSum [xForm]) z := by
  constructor
  · rw [affine_sum_defined_iff [xForm] ((1 : ℝ), 0)]
    norm_num [xForm, RationalAffineForm.value]
  · rw [affine_sum_defined_iff [xForm] ((0 : ℝ), 0)]
    norm_num [xForm, RationalAffineForm.value]

/-- Definite empty conjunction does not magically populate an empty input fiber. -/
noncomputable def zeroBounds : FunctionalBounds Unit := ⟨fun _ => 0, fun _ => 0⟩
noncomputable def vacuous : PartialEnclosure Unit := ⟨zeroBounds, allDomains []⟩

theorem empty_fiber_control :
    vacuous.UniversalSound (fun (_ : Unit) (_ : Unit) => False)
      (fun _ _ _ => False) ∧ ¬ vacuous.Sound (fun _ _ => False) := by
  constructor
  · intro _ _ h; exact False.elim h
  · intro h
    have hh := h.2.2 () (by trivial)
    simp at hh

/-- Exercise the universal bridge with a partial constant on the supplied domain. -/
theorem universal_constraint_bridge (P : Unit → Prop) :
    (PartialEnclosure.mk zeroBounds (allDomains [exactDomain P])).UniversalSound
      (fun (_ : Unit) (_ : Unit) => True) (fun p _ z => P p ∧ z = 0) := by
  apply constraints_universal [()] (fun _ => exactDomain P) (fun _ p _ => P p)
  · intro p w _ i _; exact ⟨id, id⟩
  · intro p w _; simp
  · intro p w _ z hz
    rcases hz with ⟨_, rfl⟩
    exact ⟨le_rfl, le_rfl⟩

theorem order_and_duplicates_irrelevant (p : Bool) :
    description (allDomains [yesD, noD, yesD]) p =
      description (allDomains [noD, yesD]) p := by
  apply all_description_ext
  intro D
  simp only [List.mem_cons, List.mem_singleton]
  tauto

theorem reciprocal_classification_controls :
    description (allDomains [exactDomain (fun q => xForm.value q ≠ 0)])
      ((0 : ℝ), 0) = .falseOnly ∧
    description (allDomains [exactDomain (fun q => xForm.value q ≠ 0)])
      ((1 : ℝ), 0) = .trueOnly := by
  norm_num [description, allDomains, exactDomain, DomainBounds.inter,
    xForm, RationalAffineForm.value]

end GeneralizedIntervalArithmetic.DomainConstraintsChecks
#audit_namespace GeneralizedIntervalArithmetic.DomainConstraintsChecks
