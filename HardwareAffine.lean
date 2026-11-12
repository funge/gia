import HardwareAffineProgram
import HardwareIntervalOps
import HardwareMultiplication
import LinearIntervals
import Mathlib.Analysis.Convex.Segment

namespace GeneralizedIntervalArithmetic.HardwareAffine
open HardwareAddition HardwareIntervalOps

/-- One shared parameter; endpoint uncertainty carries rounding error. -/
def Contains {F : Type} (decode : F → Option ℝ) (I : Form F) (t z : ℝ) : Prop :=
  ∃ a b, HardwareAddition.Contains decode I.atZero a ∧
    HardwareAddition.Contains decode I.atOne b ∧ z = (1-t)*a+t*b

theorem add_sound {F : Type} {decode : F → Option ℝ}
    {add : Bounds F → Bounds F → Option (Bounds F)} (ha : OpSound decode add (· + ·))
    {I J O : Form F} {t x y : ℝ}
    (hr : combine (m := Id) add I J = some O)
    (hx : Contains decode I t x) (hy : Contains decode J t y) :
    Contains decode O t (x+y) := by
  rcases hx with ⟨a,b,ha0,ha1,hx⟩
  rcases hy with ⟨c,d,hc0,hc1,hy⟩
  simp only [combine,bind,pure] at hr
  split at hr <;> try contradiction
  next A he =>
    split at hr <;> try contradiction
    next B hf =>
      cases hr
      refine ⟨a+c,b+d,ha _ _ _ _ _ he ha0 hc0,ha _ _ _ _ _ hf ha1 hc1,?_⟩
      rw [hx,hy]; ring

theorem sub_sound {F : Type} {decode : F → Option ℝ}
    {sub : Bounds F → Bounds F → Option (Bounds F)} (hs : OpSound decode sub (· - ·))
    {I J O : Form F} {t x y : ℝ}
    (hr : combine (m := Id) sub I J = some O)
    (hx : Contains decode I t x) (hy : Contains decode J t y) :
    Contains decode O t (x-y) := by
  rcases hx with ⟨a,b,ha0,ha1,hx⟩
  rcases hy with ⟨c,d,hc0,hc1,hy⟩
  simp only [combine,bind,pure] at hr
  split at hr <;> try contradiction
  next A he =>
    split at hr <;> try contradiction
    next B hf =>
      cases hr
      refine ⟨a-c,b-d,hs _ _ _ _ _ he ha0 hc0,hs _ _ _ _ _ hf ha1 hc1,?_⟩
      rw [hx,hy]; ring

theorem scale_sound {F : Type} {decode : F → Option ℝ}
    {mul : Bounds F → Bounds F → Option (Bounds F)} (hm : OpSound decode mul (· * ·))
    {I O : Form F} {C : Bounds F} {t x c : ℝ}
    (hr : scale (m := Id) mul C I = some O)
    (hc : HardwareAddition.Contains decode C c) (hx : Contains decode I t x) :
    Contains decode O t (c*x) := by
  rcases hx with ⟨a,b,ha,hb,hx⟩
  simp only [scale,bind,pure] at hr
  split at hr <;> try contradiction
  next A he =>
    split at hr <;> try contradiction
    next B hf =>
      cases hr
      refine ⟨c*a,c*b,hm _ _ _ _ _ he hc ha,hm _ _ _ _ _ hf hc hb,?_⟩
      rw [hx]; ring

theorem weighted_bounds {l u x y a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a+b=1) (hx : l ≤ x ∧ x ≤ u) (hy : l ≤ y ∧ y ≤ u) :
    l ≤ a*x+b*y ∧ a*x+b*y ≤ u := by
  constructor
  · calc l = a*l+b*l := by rw [← add_mul,hab,one_mul]
         _ ≤ a*x+b*y := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha)
           (mul_le_mul_of_nonneg_left hy.1 hb)
  · calc a*x+b*y ≤ a*u+b*u := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
           (mul_le_mul_of_nonneg_left hy.2 hb)
         _ = u := by rw [← add_mul,hab,one_mul]

theorem bounds_convex {F : Type} {decode : F → Option ℝ} {I : Bounds F}
    {x y a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (hx : HardwareAddition.Contains decode I x) (hy : HardwareAddition.Contains decode I y) :
    HardwareAddition.Contains decode I (a*x+b*y) := by
  rcases hx with ⟨l,u,hl,hu,hx⟩
  rcases hy with ⟨l',u',hl',hu',hy⟩
  have el := Option.some.inj (hl'.symm.trans hl)
  have eu := Option.some.inj (hu'.symm.trans hu)
  subst l'; subst u'
  exact ⟨l,u,hl,hu,weighted_bounds ha hb hab hx hy⟩

/-- A hardware endpoint enclosure of the rational model's endpoints encloses
EVERY value of the original linear interval, not just a central affine function. -/
theorem linear_bridge {F : Type} {decode : F → Option ℝ} {H : Form F}
    (I : LinearInterval)
    (hl0 : HardwareAddition.Contains decode H.atZero (I.lower.atZero:ℝ))
    (hu0 : HardwareAddition.Contains decode H.atZero (I.upper.atZero:ℝ))
    (hl1 : HardwareAddition.Contains decode H.atOne (I.lower.atOne:ℝ))
    (hu1 : HardwareAddition.Contains decode H.atOne (I.upper.atOne:ℝ))
    {t z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hz : I.Contains t z) :
    Contains decode H t z := by
  obtain ⟨a,b,ha,hb,hab,he⟩ := (Convex.mem_Icc (linear_ordered I ht)).mp hz
  refine ⟨a*I.lower.atZero+b*I.upper.atZero,a*I.lower.atOne+b*I.upper.atOne,
    bounds_convex ha hb hab hl0 hu0,bounds_convex ha hb hab hl1 hu1,?_⟩
  rw [← he]
  simp only [QAffine.value]
  ring

theorem exact_affine_bridge {F : Type} {decode : F → Option ℝ} {H : Form F}
    (q : QAffine) (h0 : HardwareAddition.Contains decode H.atZero (q.atZero:ℝ))
    (h1 : HardwareAddition.Contains decode H.atOne (q.atOne:ℝ)) (t : ℝ) :
    Contains decode H t (q.value t) := ⟨_,_,h0,h1,rfl⟩

theorem hull_sound {F : Type} {decode : F → Option ℝ} {mn mx : F → F → F}
    (hmin : HardwareMultiplication.SelectSound decode mn min)
    (hmax : HardwareMultiplication.SelectSound decode mx max)
    {I : Form F} {t z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hz : Contains decode I t z) :
    HardwareAddition.Contains decode (hull mn mx I) z := by
  rcases hz with ⟨a,b,ha,hb,rfl⟩
  rcases ha with ⟨l0,u0,hl0,hu0,ha⟩
  rcases hb with ⟨l1,u1,hl1,hu1,hb⟩
  refine ⟨min l0 l1,max u0 u1,hmin _ _ _ _ hl0 hl1,hmax _ _ _ _ hu0 hu1,?_⟩
  apply weighted_bounds (sub_nonneg.mpr ht.2) ht.1 (by ring)
  · exact ⟨(min_le_left _ _).trans ha.1,ha.2.trans (le_max_left _ _)⟩
  · exact ⟨(min_le_right _ _).trans hb.1,hb.2.trans (le_max_right _ _)⟩

end GeneralizedIntervalArithmetic.HardwareAffine
