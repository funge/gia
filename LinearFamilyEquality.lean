import GeneralFamilyDemotion

/-! Finite shared-parameter equality, distinct from equality of total ranges. -/
namespace GeneralizedIntervalArithmetic.LinearFamilyEquality
open FamilyDemotion

theorem fibers_equal_iff (I J : LinearInterval) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z, I.Contains t z ↔ J.Contains t z) ↔
    I.lower.atZero = J.lower.atZero ∧ I.lower.atOne = J.lower.atOne ∧
    I.upper.atZero = J.upper.atZero ∧ I.upper.atOne = J.upper.atOne := by
  constructor
  · intro h
    have a := (linear_inclusion_iff I J).mpr (fun t ht z => (h t ht z).mp)
    have b := (linear_inclusion_iff J I).mpr (fun t ht z => (h t ht z).mpr)
    exact ⟨le_antisymm b.1.1 a.1.1, le_antisymm b.1.2 a.1.2,
      le_antisymm a.2.1 b.2.1, le_antisymm a.2.2 b.2.2⟩
  · rintro ⟨h0,h1,h2,h3⟩
    have a := (linear_inclusion_iff I J).mp (by simp [h0,h1,h2,h3])
    have b := (linear_inclusion_iff J I).mp (by simp [h0,h1,h2,h3])
    exact fun t ht z => ⟨a t ht z, b t ht z⟩

/-- The existing sound affine-to-constant demotion is fiber-exact precisely
when both affine bounds are constant. No independent parameter is introduced. -/
theorem hull_fibers_equal_iff (I : LinearInterval) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      I.Contains t z ↔ (LinearInterval.constant I.hull).Contains t z) ↔
    I.lower.atZero = I.lower.atOne ∧ I.upper.atZero = I.upper.atOne := by
  rw [fibers_equal_iff]
  simp only [LinearInterval.constant, LinearInterval.hull]
  constructor
  · rintro ⟨a,b,c,d⟩
    exact ⟨a.trans b.symm, c.trans d.symm⟩
  · rintro ⟨a,b⟩
    simp [a,b]

/-- Correct sufficient-and-necessary condition for containing a supplied exact
representative: its two corresponding endpoint values must be admitted. -/
theorem exact_representative_iff (I : LinearInterval) (a b : ℚ) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨a,b⟩).Contains t z → I.Contains t z) ↔
    (I.lower.atZero ≤ a ∧ a ≤ I.upper.atZero) ∧
    (I.lower.atOne ≤ b ∧ b ≤ I.upper.atOne) := by
  rw [← linear_inclusion_iff]
  simp only [LinearInterval.exact]
  tauto

/-- All fibers stay in [0,1], and the fiber at zero already covers [0,1]. -/
def shrinking : LinearInterval :=
  ⟨⟨0,1/4⟩,⟨1,3/4⟩,by norm_num,by norm_num⟩

theorem shrinking_range : range shrinking = Set.Icc (0:ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨t,ht,hz⟩
    simp only [LinearInterval.Contains, QAffine.value, shrinking] at hz
    norm_num at hz
    constructor <;> nlinarith [ht.1,ht.2]
  · intro hz
    refine ⟨0,by norm_num,?_⟩
    simpa [LinearInterval.Contains,QAffine.value,shrinking] using hz

theorem shrinking_not_forward :
    ¬ (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨0,1⟩).Contains t z → shrinking.Contains t z) := by
  rw [exact_representative_iff]
  norm_num [shrinking]

theorem shrinking_not_reverse :
    ¬ (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨1,0⟩).Contains t z → shrinking.Contains t z) := by
  rw [exact_representative_iff]
  norm_num [shrinking]

/-- The corrected alternative: opposite endpoint extrema supply a canonical
orientation; extrema at the same endpoint supply a full endpoint fiber. -/
theorem canonical_or_full_endpoint (I : LinearInterval) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨I.hull.lo,I.hull.hi⟩).Contains t z → I.Contains t z) ∨
    (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨I.hull.hi,I.hull.lo⟩).Contains t z → I.Contains t z) ∨
    (I.lower.atZero = I.hull.lo ∧ I.upper.atZero = I.hull.hi) ∨
    (I.lower.atOne = I.hull.lo ∧ I.upper.atOne = I.hull.hi) := by
  rw [exact_representative_iff, exact_representative_iff]
  rcases le_total I.lower.atZero I.lower.atOne with hl | hl <;>
    rcases le_total I.upper.atZero I.upper.atOne with hu | hu
  · left
    simp only [LinearInterval.hull, min_eq_left hl, max_eq_right hu]
    exact ⟨⟨le_rfl,I.orderedZero⟩,⟨I.orderedOne,le_rfl⟩⟩
  · right; right; left
    simp [LinearInterval.hull,min_eq_left hl,max_eq_left hu]
  · right; right; right
    simp [LinearInterval.hull,min_eq_right hl,max_eq_right hu]
  · right; left
    simp only [LinearInterval.hull,min_eq_right hl,max_eq_left hu]
    exact ⟨⟨I.orderedZero,le_rfl⟩,⟨le_rfl,I.orderedOne⟩⟩

/-- Identifying the constant hull endpoints from an exact projected range.
The range equality is not replaced by conservative enclosure. -/
theorem hull_endpoints_of_range (I : LinearInterval) (a b : ℚ) (hab : a ≤ b)
    (hr : range I = Set.Icc (a:ℝ) b) : I.hull.lo = a ∧ I.hull.hi = b := by
  have habR : (a:ℝ) ≤ b := by exact_mod_cast hab
  have hh := constant_least I (l := (a:ℝ)) (u := (b:ℝ)) (by rw [hr])
  have hlo : (I.hull.lo:ℝ) ≤ I.hull.hi := by exact_mod_cast I.hull.ordered
  have ha := range_enclosed I (show (a:ℝ) ∈ range I by rw [hr]; exact ⟨le_rfl,habR⟩)
  have hb := range_enclosed I (show (b:ℝ) ∈ range I by rw [hr]; exact ⟨habR,le_rfl⟩)
  constructor
  · have := le_antisymm ha.1 (hh ⟨le_rfl,hlo⟩).1
    exact_mod_cast this
  · have := le_antisymm (hh ⟨hlo,le_rfl⟩).2 hb.2
    exact_mod_cast this

/-- Source-shaped corrected claim, with the full-fiber alternative explicit.
This is a derived theorem, not an assertion of authorial intent. -/
theorem canonical_or_full_fiber_of_range (I : LinearInterval) (a b : ℚ)
    (hab : a ≤ b) (hr : range I = Set.Icc (a:ℝ) b) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨a,b⟩).Contains t z → I.Contains t z) ∨
    (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      (LinearInterval.exact ⟨b,a⟩).Contains t z → I.Contains t z) ∨
    (∀ z, I.Contains 0 z ↔ z ∈ Set.Icc (a:ℝ) b) ∨
    (∀ z, I.Contains 1 z ↔ z ∈ Set.Icc (a:ℝ) b) := by
  obtain ⟨ha,hb⟩ := hull_endpoints_of_range I a b hab hr
  have h := canonical_or_full_endpoint I
  rw [ha,hb] at h
  rcases h with hf | hr | h0 | h1
  · exact Or.inl hf
  · exact Or.inr (Or.inl hr)
  · right; right; left
    intro z
    simp [LinearInterval.Contains,QAffine.value,h0.1,h0.2]
  · right; right; right
    intro z
    simp [LinearInterval.Contains,QAffine.value,h1.1,h1.2]

end GeneralizedIntervalArithmetic.LinearFamilyEquality
