import DomainProjections
import AuditPolicy

namespace GeneralizedIntervalArithmetic.DomainProjectionsChecks
open StrictComparison BooleanComposition DomainConstraints DomainProjections

def unit : QInterval := ⟨0, 1, by norm_num⟩
def oneTwo : QInterval := ⟨1, 2, by norm_num⟩
def signed : QInterval := ⟨-1, 1, by norm_num⟩

theorem projection_tables :
    Truth.falseOnly.lower = false ∧ Truth.falseOnly.upper = false ∧
    Truth.both.lower = false ∧ Truth.both.upper = true ∧
    Truth.trueOnly.lower = true ∧ Truth.trueOnly.upper = true := by decide

theorem touching : compareLE unit oneTwo = .trueOnly ∧
    compareLE oneTwo unit = .both ∧ StrictComparison.compare oneTwo unit = .falseOnly := by
  norm_num [compareLE, StrictComparison.compare, neg, unit, oneTwo]

theorem equal_singleton : compareLE (point 0) (point 0) = .trueOnly ∧
    StrictComparison.compare (point 0) (point 0) = .falseOnly := by decide

theorem negative_separation : compareLE oneTwo (point (-1)) = .falseOnly := by decide

theorem exact_touch_image : (compareLE oneTwo unit).values = leOutcomes oneTwo unit :=
  compareLE_exact _ _

theorem shared_le_not_independent :
    (∀ x : ℝ, unit.Contains x → x ≤ x) ∧ compareLE unit unit = .both := by
  constructor
  · intros; rfl
  · decide

theorem strict_and_closed_threshold :
    above 0 (point 0) = .falseOnly ∧ atLeast 0 (point 0) = .trueOnly ∧
    above 0 unit = .both ∧ atLeast 0 unit = .trueOnly ∧
    above 0 signed = .both ∧ atLeast 0 signed = .both := by decide

theorem numeric_exact_control :
    (atLeast 0 signed).values = numericImage (gePredicate 0) signed := atLeast_exact _ _

theorem projection_quantifiers :
    ((atLeast 0 signed).upper = true ↔ ∃ x, signed.Contains x ∧ gePredicate 0 x = true) ∧
    ((atLeast 0 signed).lower = true ↔ ∀ x, signed.Contains x → gePredicate 0 x = true) :=
  numeric_projections _ _ (atLeast_exact 0) _

theorem threshold_at_boundary :
    (domain (fun (_ : Unit) => above 0 unit)).Compatible () ((0 : ℝ) < 0) ∧
    (domain (fun (_ : Unit) => atLeast 0 unit)).Compatible () ((0 : ℝ) ≤ 0) := by
  simpa using threshold_compatible (fun _ => unit) 0 () 0 (by norm_num [unit, QInterval.Contains])

theorem widening_loses_certainty :
    Refines (domain (fun (_ : Unit) => atLeast 0 (point 0)))
      (domain (fun _ => atLeast 0 signed)) ∧
    atLeast 0 (point 0) ≠ atLeast 0 signed := by
  constructor
  · apply numeric_domain_refines (fun _ => point 0) (fun _ => signed)
      (gePredicate 0) (atLeast 0) (atLeast_exact 0)
    intro p x hx
    have he : x = 0 := by simpa [point] using le_antisymm hx.2 hx.1
    subst x
    norm_num [signed, QInterval.Contains]
  · decide

/-- This invalid endpoint-only classifier would discard an admitted zero. -/
noncomputable def nonzero (x : ℝ) : Bool := by
  classical
  exact decide (x ≠ 0)

theorem endpoint_sampling_failure :
    nonzero (-1) = true ∧ nonzero 1 = true ∧ signed.Contains 0 ∧
    nonzero 0 = false ∧ ¬ numericImage nonzero signed ⊆ Truth.trueOnly.values := by
  refine ⟨by simp [nonzero], by simp [nonzero], by norm_num [signed, QInterval.Contains],
    by simp [nonzero], ?_⟩
  intro h
  have hh := h (show false ∈ numericImage nonzero signed from
    ⟨0, by norm_num [signed, QInterval.Contains], by simp [nonzero]⟩)
  simp [Truth.values] at hh

theorem external_hole_sqrt :
    ((exactDomain (fun (_ : Unit) => False)).inter
      (domain (fun _ => atLeast 0 unit))).Compatible ()
        (∃ z, SqrtValues (fun (_ : Unit) (_ : Unit) y => False ∧ y = (0 : ℝ)) () () z) := by
  apply sqrt_constraint_compatible (fun _ => unit) _ () () False 0
  · exact ⟨id, id⟩
  · intro h; exact False.elim h

theorem hole_has_no_value :
    ¬ ∃ z, SqrtValues (fun (_ : Unit) (_ : Unit) y => False ∧ y = (0 : ℝ)) () () z := by
  simp [SqrtValues]

theorem sqrt_boundary_defined :
    ((exactDomain (fun (_ : Unit) => True)).inter
      (domain (fun _ => atLeast 0 (point 0)))).Compatible ()
        (∃ z, SqrtValues (fun (_ : Unit) (_ : Unit) y => True ∧ y = (0 : ℝ)) () () z) := by
  apply sqrt_constraint_compatible (fun _ => point 0) _ () () True 0
  · exact ⟨id, id⟩
  · intro _; norm_num [point, QInterval.Contains]

theorem zero_is_attained_sqrt :
    SqrtValues (fun (_ : Unit) (_ : Unit) y => True ∧ y = (0 : ℝ)) () () 0 := by
  exact ⟨0, ⟨True.intro, rfl⟩, le_rfl, by simp⟩

theorem negative_sqrt_absent :
    ¬ ∃ z, SqrtValues (fun (_ : Unit) (_ : Unit) y => True ∧ y = (-1 : ℝ)) () () z := by
  simp [SqrtValues]

/-- Sound but deliberately inexact classification need not be monotone. -/
def looseClassifier (I : QInterval) : Truth :=
  if I.lo = I.hi then .both else .trueOnly

theorem looseClassifier_sound (I : QInterval) (x : ℝ) (_hx : I.Contains x) :
    true ∈ (looseClassifier I).values := by
  unfold looseClassifier
  split_ifs <;> simp [Truth.values]

theorem sound_is_not_monotone :
    (∀ x, (point 0).Contains x → signed.Contains x) ∧
    ¬ (looseClassifier (point 0)).Refines (looseClassifier signed) := by
  constructor
  · intro x hx
    have he : x = 0 := by simpa [point] using le_antisymm hx.2 hx.1
    subst x
    norm_num [signed, QInterval.Contains]
  · norm_num [looseClassifier, point, signed, refines_iff]
    decide

end GeneralizedIntervalArithmetic.DomainProjectionsChecks
#audit_namespace GeneralizedIntervalArithmetic.DomainProjectionsChecks
