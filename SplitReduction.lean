import SplitReductionProgram
import SplitPi
import DyadicReduction

namespace GeneralizedIntervalArithmetic.HardwareSine
open HardwareAddition

theorem sweepSplit_sound {F : Type} {decode : F → Option ℝ}
    {add mul sub : Bounds F → Bounds F → Option (Bounds F)}
    (ha : OpSound decode add (· + ·)) (hm : OpSound decode mul (· * ·))
    (hs : OpSound decode sub (· - ·)) (accept : Bounds F → Bounds F → Bool)
    {kernel : Bounds F → Option (Bounds F)} (hk : RangeSound decode kernel)
    {H T : Bounds F} {h t : ℝ} (hh : Contains decode H h) (ht : Contains decode T t)
    (hpi : h+t = Real.pi) {cs : List (Bounds F)} (hc : PeriodsSound decode cs) :
    ∀ I L O x y, sweepSplit (m := Id) add mul sub accept kernel H T cs I L = some O →
      Contains decode I x → Contains decode L y → Contains decode O (Real.sin (x-y)) := by
  induction cs with
  | nil =>
    intro I L O x y hr hx hy
    simp only [sweepSplit,bind,pure] at hr
    split at hr <;> try contradiction
    next R he => exact hk R O (x-y) hr (hs I L R x y he hx hy)
  | cons C cs ih =>
    intro I L O x y hr hx hy
    have htail : PeriodsSound decode cs := fun c h => hc c (List.mem_cons_of_mem C h)
    obtain ⟨n,hn⟩ := hc C (by simp)
    simp only [sweepSplit,bind,pure] at hr
    split at hr <;> try contradiction
    next shift he =>
      split at hr
      · split at hr <;> try contradiction
        next R er =>
          split at hr <;> try contradiction
          next correction ec =>
            split at hr <;> try contradiction
            next A ea =>
              have hrx := hs I shift R _ _ er hx (hm C H shift _ _ he hn hh)
              have hay := ha L correction A _ _ ea hy (hm C T correction _ _ ec hn ht)
              have hout := ih htail R A O _ _ hr hrx hay
              have hid : (x-(n:ℝ)*2*h)-(y+(n:ℝ)*2*t) =
                  (x-y)-(n:ℝ)*(2*Real.pi) := by rw [← hpi]; ring
              simpa only [hid,Real.sin_sub_int_mul_two_pi] using hout
      · exact ih htail I L O x y hr hx hy

theorem splitRun_sound {F : Type} {decode : F → Option ℝ}
    {add mul sub : Bounds F → Bounds F → Option (Bounds F)}
    (ha : OpSound decode add (· + ·)) (hm : OpSound decode mul (· * ·))
    (hs : OpSound decode sub (· - ·)) (accept : Bounds F → Bounds F → Bool)
    {kernel : Bounds F → Option (Bounds F)} (hk : RangeSound decode kernel)
    {H T positive negative : Bounds F} {h t : ℝ}
    (hh : Contains decode H h) (ht : Contains decode T t) (hpi : h+t = Real.pi)
    (hpos : ∃ n : ℤ, Contains decode positive ((n : ℝ)*2))
    (hneg : ∃ n : ℤ, Contains decode negative ((n : ℝ)*2))
    {zero : F} (hz : decode zero = some 0) (fuel : Nat) :
    RangeSound decode (splitRun (m := Id) add mul sub accept kernel H T positive negative zero fuel) := by
  intro I O x hr hx
  simp only [splitRun,bind,pure] at hr
  split at hr <;> try contradiction
  next ps he =>
    split at hr <;> try contradiction
    next ns hn =>
      have hcs := reverse_append_periods (doubledPeriods_sound ha fuel hpos he)
        (doubledPeriods_sound ha fuel hneg hn)
      have hout := sweepSplit_sound ha hm hs accept hk hh ht hpi hcs I ⟨zero,zero⟩ O x 0 hr hx
        ⟨0,0,hz,hz,le_rfl,le_rfl⟩
      simpa only [sub_zero] using hout

end GeneralizedIntervalArithmetic.HardwareSine
