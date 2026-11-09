import UniversalDomains
import Mathlib.Data.Real.Sqrt

namespace GeneralizedIntervalArithmetic

/-- Partial real square root. Negative inputs have no value, even though
mathlib's total Real.sqrt returns zero there. -/
def SqrtValues {α W : Type*} (R : α → W → ℝ → Prop) (p : α) (w : W) (z : ℝ) : Prop :=
  ∃ x, R p w x ∧ 0 ≤ x ∧ z = Real.sqrt x

/-- Exact-real counterpart of SIGGRAPH §8's domain-tracked square-root rule.
The negative branch keeps an irrelevant payload. No rounded evaluation claim. -/
noncomputable def PartialEnclosure.sqrt {α : Type*} (I : PartialEnclosure α) : PartialEnclosure α :=
  ⟨⟨fun p => if I.values.upper p < 0 then I.values.lower p
      else Real.sqrt (max (I.values.lower p) 0),
    fun p => if I.values.upper p < 0 then I.values.upper p else Real.sqrt (I.values.upper p)⟩,
   ⟨fun p => I.domain.definite p ∧ 0 ≤ I.values.lower p ∧ 0 ≤ I.values.upper p,
    fun p => I.domain.possible p ∧ 0 ≤ I.values.upper p,
    fun p h => ⟨I.domain.consistent p h.1,h.2.2⟩⟩⟩

/-- Universal soundness includes domain compatibility for each admitted input. -/
theorem sqrt_universal_sound {α W : Type*} {I : PartialEnclosure α}
    {A : α → W → Prop} {R : α → W → ℝ → Prop}
    (h : I.UniversalSound A R) : I.sqrt.UniversalSound A (SqrtValues R) := by
  intro p w hw
  obtain ⟨hv,hd,hp⟩ := h p w hw
  refine ⟨?_,?_,?_⟩
  · rintro z ⟨x,hx,h0,rfl⟩
    have hh := hv x hx
    have hu : 0 ≤ I.values.upper p := h0.trans hh.2
    change (if I.values.upper p < 0 then _ else _) ≤ _ ∧
      _ ≤ (if I.values.upper p < 0 then _ else _)
    rw [if_neg (not_lt_of_ge hu),if_neg (not_lt_of_ge hu)]
    exact ⟨Real.sqrt_le_sqrt (max_le hh.1 h0),Real.sqrt_le_sqrt hh.2⟩
  · rintro ⟨hi,hl,_⟩
    obtain ⟨x,hx⟩ := hd hi
    exact ⟨Real.sqrt x,x,hx,hl.trans (hv x hx).1,rfl⟩
  · rintro ⟨z,x,hx,h0,_⟩
    exact ⟨hp ⟨x,hx⟩,h0.trans (hv x hx).2⟩

/-- Source branch 1: entirely negative range, arbitrary retained value payload. -/
theorem sqrt_negative_branch {α : Type*} (I : PartialEnclosure α) (p : α)
    (hu : I.values.upper p < 0) :
    I.sqrt.values.lower p = I.values.lower p ∧
    I.sqrt.values.upper p = I.values.upper p ∧
    ¬ I.sqrt.domain.definite p ∧ ¬ I.sqrt.domain.possible p := by
  simp [PartialEnclosure.sqrt,hu,not_le_of_gt hu]

/-- Source branch 2: retain the incoming domain on a nonnegative ordered range.
The explicit endpoint order excludes malformed unqualified bound pairs. -/
theorem sqrt_nonnegative_branch {α : Type*} (I : PartialEnclosure α) (p : α)
    (hl : 0 ≤ I.values.lower p) (ho : I.values.lower p ≤ I.values.upper p) :
    I.sqrt.values.lower p = Real.sqrt (I.values.lower p) ∧
    I.sqrt.values.upper p = Real.sqrt (I.values.upper p) ∧
    (I.sqrt.domain.definite p ↔ I.domain.definite p) ∧
    (I.sqrt.domain.possible p ↔ I.domain.possible p) := by
  have hu := hl.trans ho
  simp [PartialEnclosure.sqrt,not_lt_of_ge hu,max_eq_left hl,hl,hu]

/-- Source branch 3: mixed range cannot certify universal definedness. -/
theorem sqrt_mixed_branch {α : Type*} (I : PartialEnclosure α) (p : α)
    (hl : I.values.lower p < 0) (hu : 0 ≤ I.values.upper p) :
    I.sqrt.values.lower p = 0 ∧ I.sqrt.values.upper p = Real.sqrt (I.values.upper p) ∧
    ¬ I.sqrt.domain.definite p ∧
    (I.sqrt.domain.possible p ↔ I.domain.possible p) := by
  simp [PartialEnclosure.sqrt,not_lt_of_ge hu,max_eq_right (le_of_lt hl),not_le_of_gt hl,hu]

/-- Concrete partial-domain meaning, independent of any interval computation. -/
theorem sqrt_values_defined_iff {α W : Type*} (R : α → W → ℝ → Prop) (p : α) (w : W) :
    (∃ z, SqrtValues R p w z) ↔ ∃ x, R p w x ∧ 0 ≤ x := by
  constructor
  · rintro ⟨z,x,hx,h0,_⟩; exact ⟨x,hx,h0⟩
  · rintro ⟨x,hx,h0⟩; exact ⟨Real.sqrt x,x,hx,h0,rfl⟩

/-- No admitted input can produce a root when the upper range bound is negative. -/
theorem sqrt_negative_absent {α W : Type*} {I : PartialEnclosure α}
    {A : α → W → Prop} {R : α → W → ℝ → Prop}
    (h : I.UniversalSound A R) {p : α} (hu : I.values.upper p < 0) :
    ¬ ∃ w z, A p w ∧ SqrtValues R p w z := by
  rintro ⟨w,z,hw,x,hx,h0,_⟩
  exact (not_le_of_gt hu) (h0.trans ((h p w hw).1 x hx).2)

end GeneralizedIntervalArithmetic
