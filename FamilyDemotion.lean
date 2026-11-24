import ExtendedImageHull
import LinearIntervals
import FiniteAffineDemotion

/-! Mathematical representation bridges for real-valued fibers. No exceptional
comparison, machine rounding or generated demotion is specified. -/
namespace GeneralizedIntervalArithmetic.FamilyDemotion

/-- Pointwise outward bounds are equivalent to enclosing the exact closed hull
of each actual fiber, including empty and unbounded fibers. -/
theorem fiber_demotion_iff {α : Type*} (S : α → Set ℝ) (D : Set α)
    (l u : α → EReal) :
    (∀ t ∈ D, S t ⊆ ExtendedImageHull.interval (l t) (u t)) ↔
    (∀ t ∈ D, ExtendedImageHull.hull (S t) ⊆ ExtendedImageHull.interval (l t) (u t)) := by
  constructor
  · intro h t ht
    exact ExtendedImageHull.least (h t ht)
  · intro h t ht
    exact (ExtendedImageHull.sound (S t)).trans (h t ht)

/-- Actual input/output relation: the same parameter and admissible witness
survive demotion. No Cartesian independence or totality is assumed. -/
theorem relation_demotion {α β : Type*} (D : Set α) (A : α → Set β)
    (R : α → β → ℝ → Prop) (l u : α → EReal)
    (h : ∀ t ∈ D, ∀ a ∈ A t, ∀ z, R t a z →
      z ∈ ExtendedImageHull.interval (l t) (u t)) :
    ∀ t ∈ D, ExtendedImageHull.hull {z | ∃ a ∈ A t, R t a z} ⊆
      ExtendedImageHull.interval (l t) (u t) := by
  intro t ht
  exact ExtendedImageHull.relation_enclosure (A t) (R t) (h t ht)

/-- Exact hull projection preserves fiber nonemptiness; arbitrary widening need not. -/
theorem exact_fiber_domain {α : Type*} (S : α → Set ℝ) (t : α) :
    (ExtendedImageHull.hull (S t)).Nonempty ↔ (S t).Nonempty :=
  ExtendedImageHull.nonempty_iff _

/-- Four endpoint inequalities exactly characterize pointwise inclusion of
supported finite affine families, always at the SAME parameter. -/
theorem linear_inclusion_iff (I J : LinearInterval) :
    (J.lower.atZero ≤ I.lower.atZero ∧ J.lower.atOne ≤ I.lower.atOne) ∧
    (I.upper.atZero ≤ J.upper.atZero ∧ I.upper.atOne ≤ J.upper.atOne) ↔
    ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z, I.Contains t z → J.Contains t z := by
  constructor
  · rintro ⟨hl,hu⟩ t ht z hz
    exact ⟨((affine_order_iff _ _).mp hl t ht).trans hz.1,
      hz.2.trans ((affine_order_iff _ _).mp hu t ht)⟩
  · intro h
    constructor
    · apply (affine_order_iff _ _).mpr
      intro t ht
      exact (h t ht (I.lower.value t) ⟨le_rfl,linear_ordered I ht⟩).1
    · apply (affine_order_iff _ _).mpr
      intro t ht
      exact (h t ht (I.upper.value t) ⟨linear_ordered I ht,le_rfl⟩).2

/-- Forgetting the parameter, but not changing which actual values are admitted. -/
def range (I : LinearInterval) : Set ℝ :=
  {z | ∃ t ∈ Set.Icc (0:ℝ) 1, I.Contains t z}

theorem range_enclosed (I : LinearInterval) :
    range I ⊆ {z | I.hull.Contains z} := by
  rintro z ⟨t,ht,hz⟩
  exact linear_hull_encloses ht hz

/-- The existing endpoint hull is least among constant REAL closed enclosures.
This does not say the constant family preserves the original fibers. -/
theorem constant_least (I : LinearInterval) {l u : ℝ}
    (h : range I ⊆ Set.Icc l u) :
    Set.Icc (I.hull.lo:ℝ) (I.hull.hi:ℝ) ⊆ Set.Icc l u := by
  have h0l := h (show (I.lower.atZero:ℝ) ∈ range I from
    ⟨0,by norm_num,by simpa [LinearInterval.Contains,QAffine.value] using
      (show (I.lower.atZero:ℝ) ≤ I.lower.atZero ∧
        (I.lower.atZero:ℝ) ≤ I.upper.atZero from ⟨le_rfl,by exact_mod_cast I.orderedZero⟩)⟩)
  have h1l := h (show (I.lower.atOne:ℝ) ∈ range I from
    ⟨1,by norm_num,by simpa [LinearInterval.Contains,QAffine.value] using
      (show (I.lower.atOne:ℝ) ≤ I.lower.atOne ∧
        (I.lower.atOne:ℝ) ≤ I.upper.atOne from ⟨le_rfl,by exact_mod_cast I.orderedOne⟩)⟩)
  have h0u := h (show (I.upper.atZero:ℝ) ∈ range I from
    ⟨0,by norm_num,by simpa [LinearInterval.Contains,QAffine.value] using
      (show (I.lower.atZero:ℝ) ≤ I.upper.atZero ∧
        (I.upper.atZero:ℝ) ≤ I.upper.atZero from ⟨by exact_mod_cast I.orderedZero,le_rfl⟩)⟩)
  have h1u := h (show (I.upper.atOne:ℝ) ∈ range I from
    ⟨1,by norm_num,by simpa [LinearInterval.Contains,QAffine.value] using
      (show (I.lower.atOne:ℝ) ≤ I.upper.atOne ∧
        (I.upper.atOne:ℝ) ≤ I.upper.atOne from ⟨by exact_mod_cast I.orderedOne,le_rfl⟩)⟩)
  intro z hz
  have hl : l ≤ (I.hull.lo:ℝ) := by
    simp only [LinearInterval.hull,Rat.cast_min]
    exact le_min h0l.1 h1l.1
  have hu : (I.hull.hi:ℝ) ≤ u := by
    simp only [LinearInterval.hull,Rat.cast_max]
    exact max_le h0u.2 h1u.2
  exact ⟨hl.trans hz.1,hz.2.trans hu⟩

/-- Agreement with the existing generic least closed hull. -/
theorem constant_hull_exact (I : LinearInterval) :
    ExtendedImageHull.hull (range I) = {z | I.hull.Contains z} := by
  apply Set.Subset.antisymm
  · have hh := ExtendedImageHull.least (l := ((I.hull.lo:ℝ):EReal))
        (u := ((I.hull.hi:ℝ):EReal))
        (show range I ⊆ ExtendedImageHull.interval ((I.hull.lo:ℝ):EReal) ((I.hull.hi:ℝ):EReal) by
          simpa [ExtendedImageHull.interval,QInterval.Contains] using range_enclosed I)
    simpa [ExtendedImageHull.interval,QInterval.Contains] using hh
  · have hn : (range I).Nonempty :=
      ⟨I.lower.value 0,0,by norm_num,le_rfl,linear_ordered I (by norm_num)⟩
    have hb := range_enclosed I
    have hl : BddBelow (range I) := ⟨I.hull.lo,fun _ hz => (hb hz).1⟩
    have hu : BddAbove (range I) := ⟨I.hull.hi,fun _ hz => (hb hz).2⟩
    rw [ExtendedImageHull.finite_agreement hn hl hu]
    exact constant_least I (ExactImageHull.sound hl hu)

/-- Constant embedding preserves every fiber, by the existing correspondence. -/
theorem constant_embedding_exact (I : QInterval) (t : ℝ) :
    {z | (LinearInterval.constant I).Contains t z} = {z | I.Contains z} := by
  ext z
  exact linear_constant_contains I t z

/-- Compose ideal family enclosure with the existing supplied-word certificate.
The same t and actual value are retained; neither stage is claimed optimal. -/
theorem certified_relation {α : Type*} (A : ℝ → Set α)
    (R : ℝ → α → ℝ → Prop) (I : LinearInterval)
    {H O : HardwareAffine.Form Binary64.Word}
    (hc : FiniteAffineDemotion.certify I H = some O)
    (hi : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ a ∈ A t, ∀ z, R t a z → I.Contains t z)
    {t z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hz : ∃ a ∈ A t, R t a z) : HardwareAffine.Contains Binary64.real O t z := by
  obtain ⟨a,ha,hr⟩ := hz
  exact FiniteAffineDemotion.certified_enclosure hc ht (hi t ht a ha z hr)

end GeneralizedIntervalArithmetic.FamilyDemotion
