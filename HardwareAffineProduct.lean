import HardwareAffineProductProgram
import HardwareAffine
import LinearMultiplication

namespace GeneralizedIntervalArithmetic.HardwareAffine
open HardwareAddition HardwareIntervalOps

/-- Real identity behind the hardware program. Endpoints may be uncertain and
need not be the endpoints of exact rational affine functions. -/
theorem product_identity (a b c d t : ℝ) :
    ((1-t)*a+t*b)*((1-t)*c+t*d) =
    (1-t)*(a*c-(b-a)*(d-c)*(t*(1-t))) +
      t*(b*d-(b-a)*(d-c)*(t*(1-t))) := by ring

/-- Successful products enclose all pointwise witnesses, at the SAME parameter.
Only the already established interval-operation contracts are required. -/
theorem product_sound {F : Type} {decode : F → Option ℝ}
    {sub mul : Bounds F → Bounds F → Option (Bounds F)}
    (hs : OpSound decode sub (· - ·)) (hm : OpSound decode mul (· * ·))
    {bubble : Bounds F}
    (hb : ∀ u ∈ Set.Icc (0:ℝ) (1/4), HardwareAddition.Contains decode bubble u)
    {I J O : Form F} {t x y : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hr : product (m := Id) sub mul bubble I J = some O)
    (hx : Contains decode I t x) (hy : Contains decode J t y) :
    Contains decode O t (x*y) := by
  rcases hx with ⟨a,b,ha,hb',rfl⟩
  rcases hy with ⟨c,d,hc,hd,rfl⟩
  simp only [product,bind,pure] at hr
  split at hr <;> try contradiction
  next P hP =>
    simp only [combine,bind,pure] at hP
    split at hP <;> try contradiction
    next P0 hP0 =>
      split at hP <;> try contradiction
      next P1 hP1 =>
        cases hP
        simp only [combine,bind,pure] at hr
        split at hr <;> try contradiction
        next D hD =>
          split at hr <;> try contradiction
          next E hE =>
            split at hr <;> try contradiction
            next C hC =>
              split at hr <;> try contradiction
              next R hR =>
                split at hr <;> try contradiction
                next O0 hO0 =>
                  split at hr <;> try contradiction
                  next O1 hO1 =>
                    cases hr
                    have hcurv := hm _ _ _ _ _ hC (hs _ _ _ _ _ hD hb' ha)
                      (hs _ _ _ _ _ hE hd hc)
                    have hres := hm _ _ _ _ _ hR hcurv (hb _ (parameter_bubble_bounds ht))
                    exact ⟨_,_,hs _ _ _ _ _ hO0 (hm _ _ _ _ _ hP0 ha hc) hres,
                      hs _ _ _ _ _ hO1 (hm _ _ _ _ _ hP1 hb' hd) hres,
                      product_identity a b c d t⟩

/-- The constant interval [0,1/4] discharges the residual premise. Its native
binary64 endpoints are exactly representable; interpretation remains contractual. -/
theorem bubble_contains {F : Type} {decode : F → Option ℝ} {B : Bounds F}
    (hl : decode B.lo = some 0) (hu : decode B.hi = some (1/4))
    {u : ℝ} (hu' : u ∈ Set.Icc (0:ℝ) (1/4)) :
    HardwareAddition.Contains decode B u := ⟨0,1/4,hl,hu,hu'⟩

theorem product_hull_sound {F : Type} {decode : F → Option ℝ}
    {sub mul : Bounds F → Bounds F → Option (Bounds F)}
    (hs : OpSound decode sub (· - ·)) (hm : OpSound decode mul (· * ·))
    {mn mx : F → F → F}
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hx' : HardwareMultiplication.SelectSound decode mx max)
    {bubble : Bounds F}
    (hb : ∀ u ∈ Set.Icc (0:ℝ) (1/4), HardwareAddition.Contains decode bubble u)
    {I J O : Form F} {t x y : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hr : product (m := Id) sub mul bubble I J = some O)
    (hx : Contains decode I t x) (hy : Contains decode J t y) :
    HardwareAddition.Contains decode (hull mn mx O) (x*y) :=
  hull_sound hn hx' ht (product_sound hs hm hb ht hr hx hy)

end GeneralizedIntervalArithmetic.HardwareAffine
