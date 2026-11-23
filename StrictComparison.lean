import Intervals
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith

/-! Finite independent-input strict comparison, Tupper §§2.7.2 and 2.9.2.
`both` denotes two attainable outcomes for this exact comparator; it is not
an existence claim for an arbitrary conservative Boolean enclosure. -/
namespace GeneralizedIntervalArithmetic.StrictComparison

inductive Truth where
  | falseOnly | both | trueOnly
  deriving DecidableEq, Repr

/-- The three nonempty Boolean intervals, with false < true. -/
def Truth.values : Truth → Set Bool
  | .falseOnly => {false}
  | .both => Set.univ
  | .trueOnly => {true}

def Truth.lower : Truth → Bool
  | .trueOnly => true
  | _ => false

def Truth.upper : Truth → Bool
  | .falseOnly => false
  | _ => true

theorem values_eq_Icc (v : Truth) : v.values = Set.Icc v.lower v.upper := by
  cases v <;> ext b <;> cases b <;> simp [Truth.values, Truth.lower, Truth.upper]

/-- Information refinement is inclusion, not the Boolean truth order. -/
def Truth.Refines (v w : Truth) : Prop := v.values ⊆ w.values

theorem refines_iff (v w : Truth) : v.Refines w ↔ v = w ∨ w = .both := by
  cases v <;> cases w <;> simp [Truth.Refines, Truth.values, Set.subset_def]

/-- Executable endpoint decision. No floating-point operations are involved. -/
def compare (I J : QInterval) : Truth :=
  if I.hi < J.lo then .trueOnly
  else if J.hi ≤ I.lo then .falseOnly else .both

/-- Actual Boolean image of independent real witnesses. -/
noncomputable def outcomes (I J : QInterval) : Set Bool := by
  classical
  exact {b | ∃ x y : ℝ, I.Contains x ∧ J.Contains y ∧ decide (x < y) = b}

theorem true_attainable (I J : QInterval) :
    true ∈ outcomes I J ↔ I.lo < J.hi := by
  classical
  simp only [outcomes, Set.mem_setOf_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    have : (I.lo : ℝ) < J.hi := lt_of_le_of_lt hx.1 (lt_of_lt_of_le h hy.2)
    exact_mod_cast this
  · intro h
    refine ⟨I.lo, J.hi, ⟨le_rfl, ?_⟩, ⟨?_, le_rfl⟩, ?_⟩
    · exact_mod_cast I.ordered
    · exact_mod_cast J.ordered
    · exact_mod_cast h

theorem false_attainable (I J : QInterval) :
    false ∈ outcomes I J ↔ J.lo ≤ I.hi := by
  classical
  simp only [outcomes, Set.mem_setOf_eq, decide_eq_false_iff_not, not_lt]
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    have : (J.lo : ℝ) ≤ I.hi := hy.1.trans (h.trans hx.2)
    exact_mod_cast this
  · intro h
    refine ⟨I.hi, J.lo, ⟨?_, le_rfl⟩, ⟨le_rfl, ?_⟩, ?_⟩
    · exact_mod_cast I.ordered
    · exact_mod_cast J.ordered
    · exact_mod_cast h

/-- Exact image equality, including attainability rather than just enclosure. -/
theorem compare_exact (I J : QInterval) :
    (compare I J).values = outcomes I J := by
  ext b
  have hi := I.ordered
  have hj := J.ordered
  cases b
  · rw [false_attainable]
    unfold compare
    split_ifs with h h'
    · simp [Truth.values]; linarith
    · simp [Truth.values]; linarith
    · simp [Truth.values]; linarith
  · rw [true_attainable]
    unfold compare
    split_ifs with h h'
    · simp [Truth.values]; linarith
    · simp [Truth.values]; linarith
    · simp [Truth.values]; linarith

theorem compare_true_iff (I J : QInterval) :
    compare I J = .trueOnly ↔ I.hi < J.lo := by
  unfold compare
  split_ifs <;> simp_all

theorem compare_false_iff (I J : QInterval) :
    compare I J = .falseOnly ↔ J.hi ≤ I.lo := by
  have hi := I.ordered
  have hj := J.ordered
  unfold compare
  split_ifs <;> simp_all
  linarith

theorem compare_both_iff (I J : QInterval) :
    compare I J = .both ↔ I.lo < J.hi ∧ J.lo ≤ I.hi := by
  unfold compare
  split_ifs <;> simp_all

/-- Both endpoints explicitly witness the two outcomes in the mixed case. -/
theorem both_witnesses {I J : QInterval} (h : compare I J = .both) :
    (I.Contains I.lo ∧ J.Contains J.hi ∧ (I.lo : ℝ) < J.hi) ∧
    (I.Contains I.hi ∧ J.Contains J.lo ∧ (J.lo : ℝ) ≤ I.hi) := by
  rcases (compare_both_iff I J).mp h with ⟨ht, hf⟩
  have hi : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.ordered
  have hj : (J.lo : ℝ) ≤ J.hi := by exact_mod_cast J.ordered
  exact ⟨⟨⟨le_rfl, hi⟩, ⟨hj, le_rfl⟩, by exact_mod_cast ht⟩,
    ⟨⟨hi, le_rfl⟩, ⟨le_rfl, hj⟩, by exact_mod_cast hf⟩⟩

/-- Refining either independent domain can only remove possible outcomes. -/
theorem compare_refines {I J I' J' : QInterval}
    (hi : ∀ x, I'.Contains x → I.Contains x)
    (hj : ∀ y, J'.Contains y → J.Contains y) :
    (compare I' J').Refines (compare I J) := by
  rw [Truth.Refines, compare_exact, compare_exact]
  rintro b ⟨x, y, hx, hy, h⟩
  exact ⟨x, y, hi x hx, hj y hy, h⟩

end GeneralizedIntervalArithmetic.StrictComparison
