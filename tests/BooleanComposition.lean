import BooleanComposition
import AuditPolicy

namespace GeneralizedIntervalArithmetic.BooleanCompositionChecks
open StrictComparison BooleanComposition

/-- Both marginals are mixed, with the same input and its complement. -/
def opposite (p q : Bool) : Prop := q = !p

theorem opposite_marginals :
    (∀ p : Bool, ∃ q, opposite p q) ∧ (∀ q : Bool, ∃ p, opposite p q) := by
  constructor
  · intro p; exact ⟨!p, rfl⟩
  · intro q; exact ⟨!q, by cases q <;> rfl⟩

theorem shared_and_false : jointImage Bool.and opposite = {false} := by
  ext r
  cases r <;> simp [jointImage, opposite, Bool.exists_bool]

theorem shared_or_true : jointImage Bool.or opposite = {true} := by
  ext r
  cases r <;> simp [jointImage, opposite, Bool.exists_bool]

theorem independent_both :
    conj .both (neg .both) = .both ∧ disj .both (neg .both) = .both := by decide

theorem strict_loss_and :
    jointImage Bool.and opposite ⊂ (conj .both (neg .both)).values := by
  rw [shared_and_false]
  simp [conj, neg, Truth.values, Set.ssubset_def, Set.subset_def]

theorem strict_loss_or :
    jointImage Bool.or opposite ⊂ (disj .both (neg .both)).values := by
  rw [shared_or_true]
  simp [disj, neg, Truth.values, Set.ssubset_def, Set.subset_def]

/-- A hole in the joint domain yields no output; a Boolean enclosure does
not certify definedness or supply an input witness. -/
theorem empty_joint_domain (op : Bool → Bool → Bool) :
    jointImage op (fun _ _ => False) = ∅ := by
  ext r
  simp [jointImage]

theorem independent_corner_controls :
    conj .falseOnly .both = .falseOnly ∧ conj .trueOnly .both = .both ∧
    disj .trueOnly .both = .trueOnly ∧ disj .falseOnly .both = .both ∧
    neg .falseOnly = .trueOnly ∧ neg .trueOnly = .falseOnly := by decide

def unit : QInterval := ⟨0, 1, by norm_num⟩

theorem comparison_is_mixed : StrictComparison.compare unit unit = .both := by decide

theorem compared_independent_and :
    image₂ Bool.and (outcomes unit unit) (Bool.not '' outcomes unit unit) = Set.univ := by
  rw [← compare_exact, comparison_is_mixed, ← neg_exact, ← conj_exact]
  rfl

theorem compared_independent_or :
    image₂ Bool.or (outcomes unit unit) (Bool.not '' outcomes unit unit) = Set.univ := by
  rw [← compare_exact, comparison_is_mixed, ← neg_exact, ← disj_exact]
  rfl

/-- Same two real witnesses for p and its negation: it is not the independent
product of the two exact marginal outcome sets above. -/
noncomputable def comparedJoint (p q : Bool) : Prop := by
  classical
  exact ∃ x y : ℝ, unit.Contains x ∧ unit.Contains y ∧
    p = decide (x < y) ∧ q = !p

theorem compared_joint_eq : comparedJoint = opposite := by
  classical
  funext p q
  apply propext
  constructor
  · rintro ⟨x, y, _, _, _, hq⟩; exact hq
  · intro hq
    have hp : p ∈ outcomes unit unit := by
      rw [← compare_exact, comparison_is_mixed]; trivial
    rcases hp with ⟨x, y, hx, hy, hp⟩
    exact ⟨x, y, hx, hy, hp.symm, hq⟩

theorem compared_shared_controls :
    jointImage Bool.and comparedJoint = {false} ∧
    jointImage Bool.or comparedJoint = {true} := by
  rw [compared_joint_eq]
  exact ⟨shared_and_false, shared_or_true⟩

/-- A conservative mixed marginal does not imply both actual values occur. -/
theorem constant_correlated_control :
    (fun _ : Unit => false && true) '' (Set.univ : Set Unit) = {false} ∧
    (conj .both .both).values = Set.univ := by
  constructor
  · ext b; simp
  · rfl

theorem same_witness_api :
    (fun p : Bool => p && !p) '' Set.univ ⊆ (conj .both .both).values ∧
    (fun p : Bool => p || !p) '' Set.univ ⊆ (disj .both .both).values :=
  shared_witness_sound Set.univ (fun p => p) Bool.not
    (by intros; trivial) (by intros; trivial)

end GeneralizedIntervalArithmetic.BooleanCompositionChecks
#audit_namespace GeneralizedIntervalArithmetic.BooleanCompositionChecks
