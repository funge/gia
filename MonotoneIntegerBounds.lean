import BasicIntervalOps
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Archimedean

namespace GeneralizedIntervalArithmetic

/-- Monotonicity is required only on the closed input interval. No continuity
or behavior outside that interval is assumed. Endpoint bounds may be loose. -/
theorem monotone_endpoint_encloses {I R : QInterval} {f : ℝ → ℝ}
    (hm : MonotoneOn f (Set.Icc (I.lo : ℝ) I.hi))
    (hl : (R.lo : ℝ) ≤ f I.lo) (hu : f I.hi ≤ (R.hi : ℝ))
    {x : ℝ} (hx : I.Contains x) : R.Contains (f x) := by
  have ho : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.ordered
  exact ⟨hl.trans (hm ⟨le_rfl, ho⟩ hx hx.1),
    (hm hx ⟨ho, le_rfl⟩ hx.2).trans hu⟩

theorem antitone_endpoint_encloses {I R : QInterval} {f : ℝ → ℝ}
    (hm : AntitoneOn f (Set.Icc (I.lo : ℝ) I.hi))
    (hl : (R.lo : ℝ) ≤ f I.hi) (hu : f I.lo ≤ (R.hi : ℝ))
    {x : ℝ} (hx : I.Contains x) : R.Contains (f x) := by
  have ho : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.ordered
  exact ⟨hl.trans (hm hx ⟨ho, le_rfl⟩ hx.2),
    (hm ⟨le_rfl, ho⟩ hx hx.1).trans hu⟩

def QInterval.floor (I : QInterval) : QInterval :=
  ⟨(⌊I.lo⌋ : ℤ), (⌊I.hi⌋ : ℤ), by exact_mod_cast Int.floor_mono I.ordered⟩

def QInterval.ceil (I : QInterval) : QInterval :=
  ⟨(⌈I.lo⌉ : ℤ), (⌈I.hi⌉ : ℤ), by exact_mod_cast Int.ceil_mono I.ordered⟩

theorem floor_encloses {I : QInterval} {x : ℝ} (hx : I.Contains x) :
    I.floor.Contains (⌊x⌋ : ℤ) := by
  apply monotone_endpoint_encloses (f := fun x => (⌊x⌋ : ℝ)) _ _ _ hx
  · intro a _ b _ h; exact Int.cast_le.mpr (Int.floor_mono h)
  · simp [QInterval.floor]
  · simp [QInterval.floor]

theorem ceil_encloses {I : QInterval} {x : ℝ} (hx : I.Contains x) :
    I.ceil.Contains (⌈x⌉ : ℤ) := by
  apply monotone_endpoint_encloses (f := fun x => (⌈x⌉ : ℝ)) _ _ _ hx
  · intro a _ b _ h; exact Int.cast_le.mpr (Int.ceil_mono h)
  · simp [QInterval.ceil]
  · simp [QInterval.ceil]

/-- Least closed interval enclosure, not exact equality to the discrete image. -/
theorem floor_least {I R : QInterval}
    (h : ∀ x, I.Contains x → R.Contains (⌊x⌋ : ℤ)) :
    ∀ z, I.floor.Contains z → R.Contains z := by
  have ho : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.ordered
  have hl := (h I.lo ⟨le_rfl, ho⟩).1
  have hu := (h I.hi ⟨ho, le_rfl⟩).2
  intro z hz
  simp only [Rat.floor_cast] at hl hu
  simp only [QInterval.Contains, QInterval.floor, Rat.cast_intCast] at hz
  exact ⟨hl.trans hz.1, hz.2.trans hu⟩

theorem ceil_least {I R : QInterval}
    (h : ∀ x, I.Contains x → R.Contains (⌈x⌉ : ℤ)) :
    ∀ z, I.ceil.Contains z → R.Contains z := by
  have ho : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.ordered
  have hl := (h I.lo ⟨le_rfl, ho⟩).1
  have hu := (h I.hi ⟨ho, le_rfl⟩).2
  intro z hz
  simp only [Rat.ceil_cast] at hl hu
  simp only [QInterval.Contains, QInterval.ceil, Rat.cast_intCast] at hz
  exact ⟨hl.trans hz.1, hz.2.trans hu⟩

end GeneralizedIntervalArithmetic
