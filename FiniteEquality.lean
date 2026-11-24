import DomainProjections
import PartialRealArithmetic

namespace GeneralizedIntervalArithmetic.FiniteEquality
open StrictComparison BooleanComposition DomainProjections DomainConstraints

/-- Exact independent equality; overlapping intervals need not denote equal values. -/
def compareEQ (I J : QInterval) : Truth :=
  if I.lo = I.hi ∧ J.lo = J.hi ∧ I.lo = J.lo then .trueOnly
  else if I.hi < J.lo ∨ J.hi < I.lo then .falseOnly else .both

noncomputable def eqOutcomes (I J : QInterval) : Set Bool := by
  classical
  exact {b | ∃ x y : ℝ, I.Contains x ∧ J.Contains y ∧ decide (x = y) = b}

theorem eq_true_attainable (I J : QInterval) :
    true ∈ eqOutcomes I J ↔ I.lo ≤ J.hi ∧ J.lo ≤ I.hi := by
  classical
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    have he : x = y := of_decide_eq_true h
    subst y
    exact ⟨by exact_mod_cast hx.1.trans hy.2, by exact_mod_cast hy.1.trans hx.2⟩
  · rintro ⟨hij, hji⟩
    have hi : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.ordered
    have hj : (J.lo : ℝ) ≤ J.hi := by exact_mod_cast J.ordered
    have hij' : (I.lo : ℝ) ≤ J.hi := by exact_mod_cast hij
    have hji' : (J.lo : ℝ) ≤ I.hi := by exact_mod_cast hji
    exact ⟨max (I.lo : ℝ) J.lo, max (I.lo : ℝ) J.lo,
      ⟨le_max_left _ _, max_le hi hji'⟩,
      ⟨le_max_right _ _, max_le hij' hj⟩, by simp⟩

theorem eq_false_attainable (I J : QInterval) :
    false ∈ eqOutcomes I J ↔ ¬ (I.lo = I.hi ∧ J.lo = J.hi ∧ I.lo = J.lo) := by
  classical
  constructor
  · rintro ⟨x, y, hx, hy, h⟩ ⟨hi, hj, he⟩
    have hx' : x = (I.lo : ℝ) := le_antisymm (by simpa [hi] using hx.2) hx.1
    have hy' : y = (J.lo : ℝ) := le_antisymm (by simpa [hj] using hy.2) hy.1
    simp [hx', hy', he] at h
  · intro hn
    have hi := I.ordered
    have hj := J.ordered
    have h : I.lo ≠ J.hi ∨ I.hi ≠ J.lo := by
      by_contra h
      push_neg at h
      apply hn
      exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
    rcases h with h | h
    · refine ⟨I.lo, J.hi, ⟨le_rfl, by exact_mod_cast hi⟩,
        ⟨by exact_mod_cast hj, le_rfl⟩, ?_⟩
      simp only [decide_eq_false_iff_not]
      exact_mod_cast h
    · refine ⟨I.hi, J.lo, ⟨by exact_mod_cast hi, le_rfl⟩,
        ⟨le_rfl, by exact_mod_cast hj⟩, ?_⟩
      simp only [decide_eq_false_iff_not]
      exact_mod_cast h

theorem compareEQ_exact (I J : QInterval) :
    (compareEQ I J).values = eqOutcomes I J := by
  ext b
  have hi := I.ordered
  have hj := J.ordered
  cases b
  · rw [eq_false_attainable]
    unfold compareEQ
    split_ifs with h h'
    · simp only [Truth.values, Set.mem_singleton_iff, Bool.false_eq_true, false_iff, not_not]
      exact h
    · simpa only [Truth.values, Set.mem_singleton_iff, true_iff] using h
    · simpa only [Truth.values, Set.mem_univ, true_iff] using h
  · rw [eq_true_attainable]
    unfold compareEQ
    split_ifs with h h'
    · simp only [Truth.values, Set.mem_singleton_iff, true_iff]
      rcases h with ⟨a,b,c⟩
      constructor <;> linarith
    · simp only [Truth.values, Set.mem_singleton_iff, Bool.true_eq_false, false_iff, not_and]
      rcases h' with h' | h' <;> intro hh <;> linarith
    · simp only [Truth.values, Set.mem_univ, true_iff]
      push_neg at h'
      exact ⟨h'.2, h'.1⟩

def compareNE (I J : QInterval) : Truth := neg (compareEQ I J)

noncomputable def neOutcomes (I J : QInterval) : Set Bool := by
  classical
  exact {b | ∃ x y : ℝ, I.Contains x ∧ J.Contains y ∧ decide (x ≠ y) = b}

theorem compareNE_exact (I J : QInterval) :
    (compareNE I J).values = neOutcomes I J := by
  classical
  rw [compareNE, neg_exact, compareEQ_exact]
  ext b
  constructor
  · rintro ⟨c, ⟨x, y, hx, hy, hc⟩, rfl⟩
    refine ⟨x, y, hx, hy, ?_⟩
    rw [← hc]
    simp
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact ⟨decide (x = y), ⟨x,y,hx,hy,rfl⟩, by simp⟩

/-- Different numeric encodings may represent the same truth information.
The target need only be sound; the source must account for all its admitted
truths. Matching descriptor witnesses stay at the same parameter. -/
theorem reencode_refines {α : Type*} (d e : α → QInterval)
    (f g : ℝ → Bool) (c k : QInterval → Truth)
    (sourceExact : ∀ I, (c I).values = numericImage f I)
    (targetSound : ∀ I y, I.Contains y → g y ∈ (k I).values)
    (matchTruth : ∀ p x, (d p).Contains x → ∃ y, (e p).Contains y ∧ g y = f x) :
    Refines (domain (fun p => c (d p))) (domain (fun p => k (e p))) := by
  apply domain_refines
  intro p b hb
  rw [sourceExact] at hb
  rcases hb with ⟨x, hx, hxb⟩
  rcases matchTruth p x hx with ⟨y, hy, hyx⟩
  exact hxb ▸ hyx ▸ targetSound (e p) y hy

def nonzero (I : QInterval) : Truth := compareNE (point 0) I
noncomputable def nzPredicate (x : ℝ) : Bool := by
  classical
  exact decide (x ≠ 0)

theorem nonzero_exact (I : QInterval) :
    (nonzero I).values = numericImage nzPredicate I := by
  classical
  rw [nonzero, compareNE_exact]
  ext b
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    have he : x = (0 : ℝ) := by simpa [point] using le_antisymm hx.2 hx.1
    subst x
    exact ⟨y, hy, by simpa [nzPredicate, ne_comm] using h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨0,y,by norm_num [point, QInterval.Contains],hy,
      by simpa [nzPredicate, ne_comm] using h⟩

/-- Reciprocal remains partial at zero and at external input holes. -/
theorem reciprocal_constraint_compatible {α : Type*} (d : α → QInterval)
    (G : DomainBounds α) (p : α) (P : Prop) (x : ℝ)
    (hg : G.Compatible p P) (hx : P → (d p).Contains x) :
    (G.inter (domain (fun p => nonzero (d p)))).Compatible p
      (∃ z : ℝ, P ∧ PartialRealArithmetic.divRel 1 x z) := by
  have h := guarded_numeric_compatible d nzPredicate nonzero
    (fun I x hx => by rw [nonzero_exact]; exact ⟨x,hx,rfl⟩) G p P x hg hx
  simpa [nzPredicate, PartialRealArithmetic.divRel] using h

end GeneralizedIntervalArithmetic.FiniteEquality
