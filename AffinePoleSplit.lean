import GuardedPieceComposition
import SplitQuotient

/-! Exact operation-generated domain pieces for a finite affine denominator.
The pieces describe parameters, not finite enclosures of reciprocal values. -/
namespace GeneralizedIntervalArithmetic.AffinePoleSplit
open FiniteGuardPieces GuardedPieceComposition

def negative (g : Guard) (d : QAffine) : Guard := g ++ [(d,true)]
def positive (g : Guard) (d : QAffine) : Guard := g ++ [((⟨0,0⟩ : QAffine).sub d,true)]
def zero (g : Guard) (d : QAffine) : Guard :=
  g ++ [(d,false),((⟨0,0⟩ : QAffine).sub d,false)]

theorem negative_exact (g : Guard) (d : QAffine) (t : ℝ) :
    guardHolds (negative g d) t ↔ guardHolds g t ∧ d.value t < 0 := by
  rw [negative,guard_append]
  simp [guardHolds]

theorem positive_exact (g : Guard) (d : QAffine) (t : ℝ) :
    guardHolds (positive g d) t ↔ guardHolds g t ∧ 0 < d.value t := by
  rw [positive,guard_append]
  apply and_congr_right
  intro _
  have hn : ((⟨0,0⟩ : QAffine).sub d).value t = -d.value t := by
    rw [affine_sub_value]; simp [QAffine.value]
  simp [guardHolds, hn]

theorem zero_exact (g : Guard) (d : QAffine) (t : ℝ) :
    guardHolds (zero g d) t ↔ guardHolds g t ∧ d.value t = 0 := by
  rw [zero,guard_append]
  apply and_congr_right
  intro _
  have hn : ((⟨0,0⟩ : QAffine).sub d).value t = -d.value t := by
    rw [affine_sub_value]; simp [QAffine.value]
  constructor
  · intro h
    have h1 : d.value t ≤ 0 := h d false (by simp)
    have h2 : ((⟨0,0⟩ : QAffine).sub d).value t ≤ 0 :=
      h _ false (by simp)
    rw [hn] at h2
    linarith
  · intro h a strict ha
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at ha
    rcases ha with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa using le_of_eq h
    · simp [hn,h]

/-- Zero is explicitly retained as the third, undefined piece. -/
theorem partition (g : Guard) (d : QAffine) (t : ℝ) :
    guardHolds g t ↔ guardHolds (negative g d) t ∨
      guardHolds (zero g d) t ∨ guardHolds (positive g d) t := by
  rw [negative_exact,zero_exact,positive_exact]
  constructor
  · intro h
    rcases lt_trichotomy (d.value t) 0 with hn | hz | hp
    · exact Or.inl ⟨h,hn⟩
    · exact Or.inr (Or.inl ⟨h,hz⟩)
    · exact Or.inr (Or.inr ⟨h,hp⟩)
  · rintro (h | h | h) <;> exact h.1

theorem disjoint (g : Guard) (d : QAffine) (t : ℝ) :
    ¬ (guardHolds (negative g d) t ∧ guardHolds (zero g d) t) ∧
    ¬ (guardHolds (negative g d) t ∧ guardHolds (positive g d) t) ∧
    ¬ (guardHolds (zero g d) t ∧ guardHolds (positive g d) t) := by
  rw [negative_exact,zero_exact,positive_exact]
  constructor
  · rintro ⟨⟨_,hn⟩,⟨_,hz⟩⟩; linarith
  constructor
  · rintro ⟨⟨_,hn⟩,⟨_,hp⟩⟩; linarith
  · rintro ⟨⟨_,hz⟩,⟨_,hp⟩⟩; linarith

def Values (g : Guard) (d : QAffine) (t z : ℝ) : Prop :=
  guardHolds g t ∧ PartialRealArithmetic.divRel 1 (d.value t) z

def domainCode (g : Guard) (d : QAffine) : Description :=
  .union (.cell (guardAtoms (negative g d))) (.cell (guardAtoms (positive g d)))
def admitted? (g : Guard) (d : QAffine) (t : ℚ) : Bool :=
  test (domainCode g d).compile t 0

theorem domain_exact (g : Guard) (d : QAffine) (t z : ℝ) :
    z ∈ (domainCode g d).denote t ↔ ∃ v, Values g d t v := by
  change (z ∈ piece (guardAtoms (negative g d)) t ∨
    z ∈ piece (guardAtoms (positive g d)) t) ↔ _
  rw [guard_exact,guard_exact,negative_exact,positive_exact]
  simp only [Values,PartialRealArithmetic.divRel,PartialRealArithmetic.divDefined,
    PartialRealArithmetic.div,exists_and_left,exists_eq,and_true]
  constructor
  · rintro (⟨hg,hn⟩ | ⟨hg,hp⟩)
    · exact ⟨hg,ne_of_lt hn⟩
    · exact ⟨hg,ne_of_gt hp⟩
  · rintro ⟨hg,hn⟩
    rcases lt_or_gt_of_ne hn with h | h
    · exact Or.inl ⟨hg,h⟩
    · exact Or.inr ⟨hg,h⟩

theorem admitted_exact (g : Guard) (d : QAffine) (t : ℚ) :
    admitted? g d t = true ↔ ∃ z, Values g d (t:ℝ) z := by
  rw [admitted?,compiled_test_exact,domain_exact]

/-- A graph equality at the original parameter and value, not just projected inclusion. -/
theorem graph_split (g : Guard) (d : QAffine) (t z : ℝ) :
    Values g d t z ↔ Values (negative g d) d t z ∨ Values (positive g d) d t z := by
  simp only [Values,negative_exact,positive_exact]
  constructor
  · rintro ⟨hg,hn,hz⟩
    rcases lt_or_gt_of_ne hn with h | h
    · exact Or.inl ⟨⟨hg,h⟩,hn,hz⟩
    · exact Or.inr ⟨⟨hg,h⟩,hn,hz⟩
  · rintro (⟨⟨hg,_⟩,hv⟩ | ⟨⟨hg,_⟩,hv⟩) <;> exact ⟨hg,hv⟩

theorem zero_absent {g : Guard} {d : QAffine} {t : ℝ}
    (h : guardHolds (zero g d) t) : ¬ ∃ z, Values g d t z := by
  have hz := ((zero_exact g d t).1 h).2
  rintro ⟨z,_,hn,_⟩
  exact hn hz

/-- Existing partial expression semantics at the same affine coordinate. -/
theorem expression_exact (g : Guard) (d : QAffine) (t z y : ℝ) :
    Values g d t z ↔ guardHolds g t ∧
      Value (d.value t) y (.div (.const 1) .x) z := by
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨hn,rfl⟩
    simpa using (Value.div (Value.const 1) Value.x hn)
  · intro h
    cases h with
    | div ha hb hn =>
      cases ha
      cases hb
      exact ⟨hn,by simp⟩

end GeneralizedIntervalArithmetic.AffinePoleSplit
