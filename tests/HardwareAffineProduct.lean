import HardwareAffineProduct
import HardwareSine
import AuditPolicy

namespace GeneralizedIntervalArithmetic.HardwareAffineProductChecks
open HardwareAffine

theorem bubble_range {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ t*(1-t) ∧ t*(1-t) ≤ 1/4 := parameter_bubble_bounds ht

theorem bubble_extrema_attained : (0:ℝ)*(1-0)=0 ∧ (1/2:ℝ)*(1-1/2)=1/4 := by norm_num

theorem endpoint_chord_alone_is_unsound : ¬ ((1/2:ℝ)*(1-1/2) ≤ 0) := by norm_num

theorem different_parameters_break_bound : (1:ℝ)*(1-0)>1/4 := by norm_num

theorem extrapolation_breaks_bound : (2:ℝ)*(1-2)<0 := by norm_num

-- Full uncertain endpoint witnesses, not just exact affine center lines.
theorem uncertain_product {F : Type} {decode : F → Option ℝ}
    {sub mul : HardwareAddition.Bounds F → HardwareAddition.Bounds F → Option (HardwareAddition.Bounds F)}
    (hs : HardwareIntervalOps.OpSound decode sub (· - ·))
    (hm : HardwareIntervalOps.OpSound decode mul (· * ·))
    {B : HardwareAddition.Bounds F} (h0 : decode B.lo = some 0) (h1 : decode B.hi = some (1/4))
    {I J O : Form F} {t a b c d : ℝ}
    (ha : HardwareAddition.Contains decode I.atZero a)
    (hb : HardwareAddition.Contains decode I.atOne b)
    (hc : HardwareAddition.Contains decode J.atZero c)
    (hd : HardwareAddition.Contains decode J.atOne d)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hr : product (m := Id) sub mul B I J = some O) :
    Contains decode O t (((1-t)*a+t*b)*((1-t)*c+t*d)) :=
  product_sound hs hm (fun _ hu => bubble_contains h0 h1 hu) ht hr
    ⟨a,b,ha,hb,rfl⟩ ⟨c,d,hc,hd,rfl⟩

-- Directly compose existing approved primitive contracts with the new program.
theorem directed_product {F : Type} {decode : F → Option ℝ}
    {subcall mulcall : F → F → Option (F × F)} {mn mx : F → F → F}
    (hs : ∀ a b, HardwareSubtraction.CallSound decode a b (subcall a b))
    (hm : ∀ a b, HardwareMultiplication.CallSound decode a b (mulcall a b))
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hx' : HardwareMultiplication.SelectSound decode mx max)
    {B : HardwareAddition.Bounds F} (h0 : decode B.lo = some 0) (h1 : decode B.hi = some (1/4))
    {I J O : Form F} {t x y : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hr : product (m := Id)
      (fun A B => HardwareAddition.assemble (subcall A.lo B.hi) (subcall A.hi B.lo))
      (fun A B => HardwareMultiplication.assembleFour mn mx
        (mulcall A.lo B.lo) (mulcall A.lo B.hi) (mulcall A.hi B.lo) (mulcall A.hi B.hi)) B I J = some O)
    (hx : Contains decode I t x) (hy : Contains decode J t y) : Contains decode O t (x*y) :=
  product_sound (HardwareSine.sub_op_sound hs) (HardwareSine.mul_op_sound hn hx' hm)
    (fun _ hu => bubble_contains h0 h1 hu) ht hr hx hy

-- Composable output: the next multiplication is justified at the same witness.
theorem composed_product {F : Type} {decode : F → Option ℝ}
    {sub mul : HardwareAddition.Bounds F → HardwareAddition.Bounds F → Option (HardwareAddition.Bounds F)}
    (hs : HardwareIntervalOps.OpSound decode sub (· - ·))
    (hm : HardwareIntervalOps.OpSound decode mul (· * ·))
    {B : HardwareAddition.Bounds F}
    (hb : ∀ u ∈ Set.Icc (0:ℝ) (1/4), HardwareAddition.Contains decode B u)
    {I J K P O : Form F} {t x y z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hp : product (m := Id) sub mul B I J = some P)
    (ho : product (m := Id) sub mul B P K = some O)
    (hx : Contains decode I t x) (hy : Contains decode J t y) (hz : Contains decode K t z) :
    Contains decode O t ((x*y)*z) :=
  product_sound hs hm hb ht ho (product_sound hs hm hb ht hp hx hy) hz

#audit_namespace GeneralizedIntervalArithmetic.HardwareAffineProductChecks
end GeneralizedIntervalArithmetic.HardwareAffineProductChecks
