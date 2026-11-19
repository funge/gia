import PartialEnclosures
import Mathlib.Data.Real.Archimedean

namespace GeneralizedIntervalArithmetic.IntegerResidue

/-- Provenance of an actual value, not of its enclosing endpoints. -/
def IntegerValue (z : ℝ) : Prop := ∃ n : ℤ, z = n

def HasResidue (d r : ℤ) (z : ℝ) : Prop := ∃ k : ℤ, z = ((r + d*k : ℤ) : ℝ)

theorem floor_integer (x : ℝ) : IntegerValue (⌊x⌋ : ℤ) := ⟨⌊x⌋, rfl⟩
theorem ceil_integer (x : ℝ) : IntegerValue (⌈x⌉ : ℤ) := ⟨⌈x⌉, rfl⟩

theorem integer_add {x y : ℝ} (hx : IntegerValue x) (hy : IntegerValue y) : IntegerValue (x+y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a+b, by push_cast; rfl⟩

theorem integer_sub {x y : ℝ} (hx : IntegerValue x) (hy : IntegerValue y) : IntegerValue (x-y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a-b, by push_cast; rfl⟩

theorem integer_scale (a : ℤ) {x : ℝ} (hx : IntegerValue x) : IntegerValue (a*x) := by
  obtain ⟨n,rfl⟩ := hx
  exact ⟨a*n, by push_cast; rfl⟩

theorem affine_residue {x : ℝ} (hx : IntegerValue x) (a b d r : ℤ)
    (ha : d ∣ a) (hb : d ∣ b-r) : HasResidue d r (a*x+b) := by
  obtain ⟨n,rfl⟩ := hx
  obtain ⟨u,hu⟩ := ha
  obtain ⟨v,hv⟩ := hb
  refine ⟨u*n+v, ?_⟩
  have he : a*n+b = r+d*(u*n+v) := by rw [hu]; nlinarith [hv]
  exact_mod_cast he

theorem residue_add {x y : ℝ} {d r s : ℤ}
    (hx : HasResidue d r x) (hy : HasResidue d s y) : HasResidue d (r+s) (x+y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  refine ⟨a+b, ?_⟩
  push_cast
  ring

theorem residue_sub {x y : ℝ} {d r s : ℤ}
    (hx : HasResidue d r x) (hy : HasResidue d s y) : HasResidue d (r-s) (x-y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  refine ⟨a-b, ?_⟩
  push_cast
  ring

theorem residue_scale (a : ℤ) {x : ℝ} {d r : ℤ}
    (hx : HasResidue d r x) : HasResidue d (a*r) (a*x) := by
  obtain ⟨k,rfl⟩ := hx
  refine ⟨a*k, ?_⟩
  push_cast
  ring

/-- Closed endpoints: strict separation of integer ceil/floor bounds is required. -/
theorem window_exclusion {d r : ℤ} (hd : 0 < d) {z L U : ℝ}
    (hz : HasResidue d r z)
    (gap : ⌊(U-r)/d⌋ < ⌈(L-r)/d⌉) : ¬ (L ≤ z ∧ z ≤ U) := by
  obtain ⟨k,rfl⟩ := hz
  intro h
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo : (L-r)/d ≤ (k : ℝ) := (div_le_iff₀ hdR).mpr (by push_cast at h; nlinarith [h.1])
  have hhi : (k : ℝ) ≤ (U-r)/d := (le_div_iff₀ hdR).mpr (by push_cast at h; nlinarith [h.2])
  exact (not_le_of_gt gap) ((Int.ceil_le.mpr hlo).trans (Int.le_floor.mpr hhi))

/-- Applies to actual values at the same parameter; does not assert existence. -/
theorem relation_exclusion {α : Type*} {R : α → ℝ → Prop} {p : α}
    {d r : ℤ} (hd : 0 < d) {L U : ℝ}
    (residue : ∀ z, R p z → HasResidue d r z)
    (gap : ⌊(U-r)/d⌋ < ⌈(L-r)/d⌉) : ¬ ∃ z, R p z ∧ L ≤ z ∧ z ≤ U := by
  rintro ⟨z,hz,hwindow⟩
  exact window_exclusion hd (residue z hz) gap hwindow

/-- Combine numerical bounds and residues for the same semantic value. -/
theorem enclosure_window_exclusion {α : Type*} {I : PartialEnclosure α}
    {R : α → ℝ → Prop} (sound : I.Sound R) {p : α} {d r : ℤ} (hd : 0 < d)
    (residue : ∀ z, R p z → HasResidue d r z) {L U : ℝ}
    (gap : ⌊(min U (I.values.upper p)-r)/d⌋ <
      ⌈(max L (I.values.lower p)-r)/d⌉) : ¬ ∃ z, R p z ∧ L ≤ z ∧ z ≤ U := by
  rintro ⟨z,hz,hL,hU⟩
  exact window_exclusion hd (residue z hz) gap
    ⟨max_le hL (sound.1 p z hz).1, le_min hU (sound.1 p z hz).2⟩
end GeneralizedIntervalArithmetic.IntegerResidue
