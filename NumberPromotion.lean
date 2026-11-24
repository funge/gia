import ExceptionalComparisons
import Mathlib.Algebra.Order.Floor.Ring

/-! Mathematical outward demotion to extended integer endpoints. This is not
an IEEE conversion or Tupper's exceptional numerical comparison relation. -/
namespace GeneralizedIntervalArithmetic.NumberPromotion

noncomputable def down : EReal → EReal := EReal.rec ⊥ (fun x => ((⌊x⌋ : ℤ) : ℝ)) ⊤
noncomputable def up : EReal → EReal := EReal.rec ⊥ (fun x => ((⌈x⌉ : ℤ) : ℝ)) ⊤
def IntegerBound (b : EReal) : Prop := b = ⊥ ∨ b = ⊤ ∨ ∃ z : ℤ, b = ((z : ℝ) : EReal)

theorem down_le (x : EReal) : down x ≤ x := by
  induction x using EReal.rec with
  | bot => exact le_rfl
  | top => exact le_rfl
  | coe r => exact EReal.coe_le_coe_iff.mpr (Int.floor_le r)

theorem le_up (x : EReal) : x ≤ up x := by
  induction x using EReal.rec with
  | bot => exact le_rfl
  | top => exact le_rfl
  | coe r => exact EReal.coe_le_coe_iff.mpr (Int.le_ceil r)

theorem down_greatest {a x : EReal} (ha : IntegerBound a) (h : a ≤ x) : a ≤ down x := by
  rcases ha with rfl | rfl | ⟨z,rfl⟩
  · exact bot_le
  · have hx : x = ⊤ := top_le_iff.mp h
    subst x
    exact le_rfl
  · induction x using EReal.rec with
    | bot => simp at h
    | top => exact le_top
    | coe r =>
      apply EReal.coe_le_coe_iff.mpr
      exact_mod_cast (Int.le_floor.mpr (EReal.coe_le_coe_iff.mp h))

theorem up_least {b x : EReal} (hb : IntegerBound b) (h : x ≤ b) : up x ≤ b := by
  rcases hb with rfl | rfl | ⟨z,rfl⟩
  · have hx : x = ⊥ := le_bot_iff.mp h
    subst x
    exact le_rfl
  · exact le_top
  · induction x using EReal.rec with
    | bot => exact bot_le
    | top => simp at h
    | coe r =>
      apply EReal.coe_le_coe_iff.mpr
      exact_mod_cast (Int.ceil_le.mpr (EReal.coe_le_coe_iff.mp h))

theorem down_integer (x : EReal) : IntegerBound (down x) := by
  induction x using EReal.rec with
  | bot => exact Or.inl rfl
  | top => exact Or.inr (Or.inl rfl)
  | coe r => exact Or.inr (Or.inr ⟨⌊r⌋,rfl⟩)

theorem up_integer (x : EReal) : IntegerBound (up x) := by
  induction x using EReal.rec with
  | bot => exact Or.inl rfl
  | top => exact Or.inr (Or.inl rfl)
  | coe r => exact Or.inr (Or.inr ⟨⌈r⌉,rfl⟩)

theorem fixed {x : EReal} (h : IntegerBound x) : down x = x ∧ up x = x :=
  ⟨le_antisymm (down_le x) (down_greatest h le_rfl),
   le_antisymm (up_least h le_rfl) (le_up x)⟩

noncomputable def hull (S : Set ℝ) : Set ℝ :=
  ExtendedImageHull.interval (down (ExtendedImageHull.lower S)) (up (ExtendedImageHull.upper S))

theorem sound (S : Set ℝ) : S ⊆ hull S := by
  intro x hx
  have h := ExtendedImageHull.sound S hx
  exact ⟨(down_le _).trans h.1, h.2.trans (le_up _)⟩

theorem least {S : Set ℝ} {l u : EReal} (hl : IntegerBound l) (hu : IntegerBound u)
    (h : S ⊆ ExtendedImageHull.interval l u) : hull S ⊆ ExtendedImageHull.interval l u := by
  have he := ExtendedImageHull.endpoint_least h
  intro x hx
  exact ⟨(down_greatest hl he.1).trans hx.1, hx.2.trans (up_least hu he.2)⟩

theorem mono {S T : Set ℝ} (h : S ⊆ T) : hull S ⊆ hull T :=
  least (down_integer _) (up_integer _) (h.trans (sound T))

theorem empty : hull ∅ = ∅ := by
  change ExtendedImageHull.interval (down (ExtendedImageHull.lower ∅))
    (up (ExtendedImageHull.upper ∅)) = ∅
  rw [ExtendedImageHull.empty_bounds.1, ExtendedImageHull.empty_bounds.2]
  change ExtendedImageHull.interval ⊤ ⊥ = ∅
  ext x
  simp [ExtendedImageHull.interval]

/-- Only actual outputs enter the hull: this does not create values at holes. -/
theorem relation_sound {α : Type*} (D : Set α) (R : α → ℝ → Prop)
    {a : α} {y : ℝ} (ha : a ∈ D) (hy : R a y) :
    y ∈ hull {v | ∃ x ∈ D, R x v} := sound _ ⟨a,ha,hy⟩

theorem finite_formula {S : Set ℝ} (hne : S.Nonempty)
    (hl : BddBelow S) (hu : BddAbove S) :
    hull S = ExtendedImageHull.interval
      (((⌊sInf S⌋ : ℤ) : ℝ) : EReal) (((⌈sSup S⌉ : ℤ) : ℝ) : EReal) := by
  unfold hull
  rw [ExtendedImageHull.lower_finite hne hl, ExtendedImageHull.upper_finite hne hu]
  rfl

noncomputable def promoteInt (z : ℤ) : ExceptionalComparisons.Value := .finite z
noncomputable def promoteRat (q : ℚ) : ExceptionalComparisons.Value := .finite q

theorem promotion_coherent (z : ℤ) : promoteRat z = promoteInt z := by
  simp [promoteRat, promoteInt]

theorem promoteInt_injective : Function.Injective promoteInt := by
  intro a b h
  have h' : (a : ℝ) = (b : ℝ) := ExceptionalComparisons.Value.finite.inj h
  exact_mod_cast h'

theorem promoteRat_injective : Function.Injective promoteRat := by
  intro a b h
  have h' : (a : ℝ) = (b : ℝ) := ExceptionalComparisons.Value.finite.inj h
  exact_mod_cast h'

theorem integer_bound_correspondence (z : ℤ) :
    ExceptionalComparisons.bound (promoteInt z) = some ((z : ℝ) : EReal) := rfl

/-- Source finite promotion preserves each of the five named real predicates.
This uses exact rational casts, not rounded arithmetic or exceptional tags. -/
theorem rational_comparisons (p q : ℚ) :
    ExceptionalComparisons.observe .lt (promoteRat p) (promoteRat q) = some (decide (p < q)) ∧
    ExceptionalComparisons.observe .le (promoteRat p) (promoteRat q) = some (decide (p ≤ q)) ∧
    ExceptionalComparisons.observe .eq (promoteRat p) (promoteRat q) = some (decide (p = q)) ∧
    ExceptionalComparisons.observe .ge (promoteRat p) (promoteRat q) = some (decide (q ≤ p)) ∧
    ExceptionalComparisons.observe .gt (promoteRat p) (promoteRat q) = some (decide (q < p)) := by
  simp [promoteRat, ExceptionalComparisons.observe, ExceptionalComparisons.finiteMeaning]

end GeneralizedIntervalArithmetic.NumberPromotion
