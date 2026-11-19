import EndpointChords
import Mathlib.Analysis.Convex.Deriv

namespace GeneralizedIntervalArithmetic.TangentBounds
open EndpointChords

/-- A real tangent with an explicit, certified derivative value. -/
def tangent (f : ℝ → ℝ) (p d x : ℝ) : ℝ := f p+d*(x-p)

theorem tangent_at (f : ℝ → ℝ) (p d : ℝ) : tangent f p d p = f p := by simp [tangent]

theorem tangent_blend (f : ℝ → ℝ) (p d a b t : ℝ) :
    tangent f p d (blend a b t) = blend (tangent f p d a) (tangent f p d b) t := by
  dsimp [tangent,blend]; ring

/-- Finite-domain supporting tangent: only differentiability within the domain
at the contact point is required, including one-sided endpoint derivatives. -/
theorem convex_lower {f : ℝ → ℝ} {a b p d x : ℝ}
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hp : p ∈ Set.Icc a b)
    (hd : HasDerivWithinAt f d (Set.Icc a b) p) (hx : x ∈ Set.Icc a b) :
    tangent f p d x ≤ f x := by
  rcases lt_trichotomy p x with h | h | h
  · have hs := hf.le_slope_of_hasDerivWithinAt hp hx h hd
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    dsimp [tangent]; linarith
  · subst x; simp [tangent]
  · have hs := hf.slope_le_of_hasDerivWithinAt hx hp h hd
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    dsimp [tangent]; nlinarith

/-- Tupper §3.3.11's differentiable concave upper tangent, via negation duality. -/
theorem concave_upper {f : ℝ → ℝ} {a b p d x : ℝ}
    (hf : ConcaveOn ℝ (Set.Icc a b) f) (hp : p ∈ Set.Icc a b)
    (hd : HasDerivWithinAt f d (Set.Icc a b) p) (hx : x ∈ Set.Icc a b) :
    f x ≤ tangent f p d x := by
  have hn : ConvexOn ℝ (Set.Icc a b) (-f) := neg_convexOn_iff.mpr hf
  have h := convex_lower hn hp hd.neg hx
  simp only [tangent,Pi.neg_apply,neg_mul] at h ⊢
  linarith

/-- A singleton needs neither a derivative certificate nor curvature. -/
theorem singleton (f : ℝ → ℝ) {a x : ℝ} (d : ℝ) (hx : x ∈ Set.Icc a a) :
    tangent f a d x = f x := by
  have h : x = a := le_antisymm hx.2 hx.1
  subst x; exact tangent_at _ _ _

/-- Outward endpoint certificates enclose the whole affine tangent; rounding
a slope in one fixed direction alone would not suffice on both sides of p. -/
theorem outward_lower {f : ℝ → ℝ} {a b p d t l r : ℝ}
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hp : p ∈ Set.Icc a b)
    (hd : HasDerivWithinAt f d (Set.Icc a b) p)
    (hl : l ≤ tangent f p d a) (hr : r ≤ tangent f p d b)
    (ht : t ∈ Set.Icc (0:ℝ) 1) : blend l r t ≤ f (blend a b t) := by
  have h := blend_mono hl hr ht
  rw [← tangent_blend] at h
  exact h.trans (convex_lower hf hp hd (blend_mem (hp.1.trans hp.2) ht))

theorem outward_upper {f : ℝ → ℝ} {a b p d t u v : ℝ}
    (hf : ConcaveOn ℝ (Set.Icc a b) f) (hp : p ∈ Set.Icc a b)
    (hd : HasDerivWithinAt f d (Set.Icc a b) p)
    (hu : tangent f p d a ≤ u) (hv : tangent f p d b ≤ v)
    (ht : t ∈ Set.Icc (0:ℝ) 1) : f (blend a b t) ≤ blend u v t := by
  have h := blend_mono hu hv ht
  rw [← tangent_blend] at h
  exact (concave_upper hf hp hd (blend_mem (hp.1.trans hp.2) ht)).trans h

/-- Combine the tangent lower side with the previously proved exact upper chord. -/
theorem convex_sandwich {f : ℝ → ℝ} {a b p d t : ℝ}
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hp : p ∈ Set.Icc a b)
    (hd : HasDerivWithinAt f d (Set.Icc a b) p) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    tangent f p d (blend a b t) ≤ f (blend a b t) ∧
      f (blend a b t) ≤ blend (f a) (f b) t :=
  ⟨convex_lower hf hp hd (blend_mem (hp.1.trans hp.2) ht),
    EndpointChords.convex_upper (hp.1.trans hp.2) hf ht⟩

theorem concave_sandwich {f : ℝ → ℝ} {a b p d t : ℝ}
    (hf : ConcaveOn ℝ (Set.Icc a b) f) (hp : p ∈ Set.Icc a b)
    (hd : HasDerivWithinAt f d (Set.Icc a b) p) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    blend (f a) (f b) t ≤ f (blend a b t) ∧
      f (blend a b t) ≤ tangent f p d (blend a b t) :=
  ⟨EndpointChords.concave_lower (hp.1.trans hp.2) hf ht,
    concave_upper hf hp hd (blend_mem (hp.1.trans hp.2) ht)⟩

end GeneralizedIntervalArithmetic.TangentBounds
