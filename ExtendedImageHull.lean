import ExactImageHull
import Mathlib.Data.EReal.Basic

/-! Extended bounds for actual REAL outputs. No exceptional arithmetic is used.
The empty image has canonical reversed bounds top/bottom and no real members. -/
namespace GeneralizedIntervalArithmetic.ExtendedImageHull

noncomputable def lower (S : Set ℝ) : EReal := sInf (Real.toEReal '' S)
noncomputable def upper (S : Set ℝ) : EReal := sSup (Real.toEReal '' S)
def interval (l u : EReal) : Set ℝ := {x | l ≤ (x : EReal) ∧ (x : EReal) ≤ u}
noncomputable def hull (S : Set ℝ) : Set ℝ := interval (lower S) (upper S)

theorem sound (S : Set ℝ) : S ⊆ hull S :=
  fun x hx => ⟨sInf_le ⟨x,hx,rfl⟩, le_sSup ⟨x,hx,rfl⟩⟩

theorem endpoint_least {S : Set ℝ} {l u : EReal} (h : S ⊆ interval l u) :
    l ≤ lower S ∧ upper S ≤ u := by
  constructor
  · apply le_sInf
    rintro _ ⟨x,hx,rfl⟩
    exact (h hx).1
  · apply sSup_le
    rintro _ ⟨x,hx,rfl⟩
    exact (h hx).2

theorem least {S : Set ℝ} {l u : EReal} (h : S ⊆ interval l u) :
    hull S ⊆ interval l u := by
  intro x hx
  have he := endpoint_least h
  exact ⟨he.1.trans hx.1,hx.2.trans he.2⟩

theorem enclosure_iff (S : Set ℝ) (l u : EReal) :
    S ⊆ interval l u ↔ hull S ⊆ interval l u :=
  ⟨least,fun h => (sound S).trans h⟩

theorem mono {S T : Set ℝ} (h : S ⊆ T) : hull S ⊆ hull T :=
  least (h.trans (sound T))

theorem ordered_iff (S : Set ℝ) : lower S ≤ upper S ↔ S.Nonempty := by
  constructor
  · intro h
    by_contra hn
    have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [he,lower,upper] at h
  · rintro ⟨x,hx⟩
    exact (sound S hx).1.trans (sound S hx).2

theorem empty_bounds : lower ∅ = ⊤ ∧ upper ∅ = ⊥ := by simp [lower,upper]
theorem empty_hull : hull ∅ = ∅ := by
  ext x
  simp [hull,interval,lower,upper]

theorem nonempty_iff (S : Set ℝ) : (hull S).Nonempty ↔ S.Nonempty := by
  constructor
  · rintro ⟨x,hx⟩
    exact (ordered_iff S).mp (hx.1.trans hx.2)
  · exact fun ⟨x,hx⟩ => ⟨x,sound S hx⟩

/-- No attainment premise: the endpoints may be limits or infinite bounds. -/
theorem lower_finite {S : Set ℝ} (hne : S.Nonempty) (hb : BddBelow S) :
    lower S = (sInf S : ℝ) := by
  apply le_antisymm
  · have hbound : ∀ x ∈ S, lower S ≤ (x : EReal) := fun x hx => (sound S hx).1
    generalize he : lower S = l at hbound ⊢
    induction l using EReal.rec with
    | bot => exact bot_le
    | top =>
      obtain ⟨x,hx⟩ := hne
      exact False.elim ((not_le_of_gt (EReal.coe_lt_top x)) (hbound x hx))
    | coe r =>
      exact EReal.coe_le_coe_iff.mpr (le_csInf hne (fun x hx =>
        EReal.coe_le_coe_iff.mp (hbound x hx)))
  · apply le_sInf
    rintro _ ⟨x,hx,rfl⟩
    exact EReal.coe_le_coe_iff.mpr (csInf_le hb hx)

theorem upper_finite {S : Set ℝ} (hne : S.Nonempty) (hb : BddAbove S) :
    upper S = (sSup S : ℝ) := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨x,hx,rfl⟩
    exact EReal.coe_le_coe_iff.mpr (le_csSup hb hx)
  · have hbound : ∀ x ∈ S, (x : EReal) ≤ upper S := fun x hx => (sound S hx).2
    generalize he : upper S = u at hbound ⊢
    induction u using EReal.rec with
    | bot =>
      obtain ⟨x,hx⟩ := hne
      exact False.elim ((not_le_of_gt (EReal.bot_lt_coe x)) (hbound x hx))
    | top => exact le_top
    | coe r =>
      exact EReal.coe_le_coe_iff.mpr (csSup_le hne (fun x hx =>
        EReal.coe_le_coe_iff.mp (hbound x hx)))

theorem finite_agreement {S : Set ℝ} (hne : S.Nonempty)
    (hl : BddBelow S) (hu : BddAbove S) : hull S = ExactImageHull.hull S := by
  ext x
  simp [hull,interval,lower_finite hne hl,upper_finite hne hu,ExactImageHull.hull]

theorem lower_unbounded {S : Set ℝ} (h : ¬ BddBelow S) : lower S = ⊥ := by
  have hb : ∀ x ∈ S, lower S ≤ (x : EReal) := fun x hx => (sound S hx).1
  generalize he : lower S = l at hb ⊢
  induction l using EReal.rec with
  | bot => rfl
  | coe r => exact False.elim (h ⟨r,fun x hx => EReal.coe_le_coe_iff.mp (hb x hx)⟩)
  | top =>
    apply False.elim
    apply h
    exact ⟨0,fun x hx => False.elim ((not_le_of_gt (EReal.coe_lt_top x)) (hb x hx))⟩

theorem upper_unbounded {S : Set ℝ} (h : ¬ BddAbove S) : upper S = ⊤ := by
  have hb : ∀ x ∈ S, (x : EReal) ≤ upper S := fun x hx => (sound S hx).2
  generalize he : upper S = u at hb ⊢
  induction u using EReal.rec with
  | top => rfl
  | coe r => exact False.elim (h ⟨r,fun x hx => EReal.coe_le_coe_iff.mp (hb x hx)⟩)
  | bot =>
    apply False.elim
    apply h
    exact ⟨0,fun x hx => False.elim ((not_le_of_gt (EReal.bot_lt_coe x)) (hb x hx))⟩

theorem interval_fixed (l u : EReal) : hull (interval l u) = interval l u :=
  Set.Subset.antisymm (least (Set.Subset.refl _)) (sound _)

theorem idempotent (S : Set ℝ) : hull (hull S) = hull S := interval_fixed _ _

/-- Relation images keep one admissible input and do not assert totality. -/
theorem relation_enclosure {α : Type*} (A : Set α) (R : α → ℝ → Prop)
    {l u : EReal} (h : ∀ a ∈ A, ∀ z, R a z → z ∈ interval l u) :
    hull {z | ∃ a ∈ A, R a z} ⊆ interval l u := by
  apply least
  rintro z ⟨a,ha,hz⟩
  exact h a ha z hz

end GeneralizedIntervalArithmetic.ExtendedImageHull
