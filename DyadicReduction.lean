import DyadicReductionProgram
import SineReduction

namespace GeneralizedIntervalArithmetic.HardwareSine
open HardwareAddition

theorem doubledPeriods_sound {F : Type} {decode : F → Option ℝ}
    {add : Bounds F → Bounds F → Option (Bounds F)}
    (ha : OpSound decode add (· + ·)) (fuel : Nat) {C : Bounds F}
    (hc : ∃ n : ℤ, Contains decode C ((n : ℝ)*2))
    {cs : List (Bounds F)} (hr : doubledPeriods (m := Id) add fuel C = some cs) :
    PeriodsSound decode cs := by
  induction fuel generalizing C cs with
  | zero => simp only [doubledPeriods,pure] at hr; cases hr; simp [PeriodsSound]
  | succ fuel ih =>
    simp only [doubledPeriods,bind,pure] at hr
    split at hr <;> try contradiction
    next D hd =>
      split at hr <;> try contradiction
      next rest he =>
        cases hr
        obtain ⟨n,hn⟩ := hc
        have hD : Contains decode D (((n+n : ℤ) : ℝ)*2) := by
          convert ha C C D _ _ hd hn hn using 1
          push_cast
          ring
        have hs := ih ⟨n+n,hD⟩ he
        intro c hmem
        rcases List.mem_cons.mp hmem with h | h
        · subst c; exact ⟨n,hn⟩
        · exact hs c h

theorem sweepPeriods_sound {F : Type} {decode : F → Option ℝ}
    {mul sub : Bounds F → Bounds F → Option (Bounds F)}
    (hm : OpSound decode mul (· * ·)) (hs : OpSound decode sub (· - ·))
    (accept : Bounds F → Bounds F → Bool)
    {kernel : Bounds F → Option (Bounds F)} (hk : RangeSound decode kernel)
    {P : Bounds F} (hp : Contains decode P Real.pi)
    {cs : List (Bounds F)} (hc : PeriodsSound decode cs) :
    RangeSound decode (sweepPeriods (m := Id) mul sub accept kernel P cs) := by
  induction cs with
  | nil => exact hk
  | cons C cs ih =>
    intro I O x hr hx
    have htail : PeriodsSound decode cs := fun c h => hc c (List.mem_cons_of_mem C h)
    obtain ⟨n,hn⟩ := hc C (by simp)
    simp only [sweepPeriods,bind,pure] at hr
    split at hr <;> try contradiction
    next shift he =>
      split at hr
      · split at hr <;> try contradiction
        next R er =>
          have hR := hs I shift R _ _ er hx (hm C P shift _ _ he hn hp)
          have hout := ih htail R O _ hr hR
          have hid : x - (n : ℝ)*2*Real.pi = x - (n : ℝ)*(2*Real.pi) := by ring
          simpa only [hid,Real.sin_sub_int_mul_two_pi] using hout
      · exact ih htail I O x hr hx

theorem reverse_append_periods {F : Type} {decode : F → Option ℝ}
    {ps ns : List (Bounds F)} (hp : PeriodsSound decode ps) (hn : PeriodsSound decode ns) :
    PeriodsSound decode (ps.reverse ++ ns.reverse) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact hp c (List.mem_reverse.mp h)
  · exact hn c (List.mem_reverse.mp h)

theorem dyadicRun_sound {F : Type} {decode : F → Option ℝ}
    {add mul sub : Bounds F → Bounds F → Option (Bounds F)}
    (ha : OpSound decode add (· + ·)) (hm : OpSound decode mul (· * ·))
    (hs : OpSound decode sub (· - ·)) (accept : Bounds F → Bounds F → Bool)
    {kernel : Bounds F → Option (Bounds F)} (hk : RangeSound decode kernel)
    {P positive negative : Bounds F} (hp : Contains decode P Real.pi)
    (hpos : ∃ n : ℤ, Contains decode positive ((n : ℝ)*2))
    (hneg : ∃ n : ℤ, Contains decode negative ((n : ℝ)*2)) (fuel : Nat) :
    RangeSound decode (dyadicRun (m := Id) add mul sub accept kernel P positive negative fuel) := by
  intro I O x hr hx
  simp only [dyadicRun,bind,pure] at hr
  split at hr <;> try contradiction
  next ps he =>
    split at hr <;> try contradiction
    next ns hn =>
      exact sweepPeriods_sound hm hs accept hk hp
        (reverse_append_periods (doubledPeriods_sound ha fuel hpos he)
          (doubledPeriods_sound ha fuel hneg hn)) I O x hr hx

end GeneralizedIntervalArithmetic.HardwareSine
