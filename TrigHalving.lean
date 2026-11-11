import TrigHalvingProgram
import HardwareCosine
import HardwareCover

namespace GeneralizedIntervalArithmetic.HardwareHalving
open HardwareAddition HardwareSine

theorem run_sound {F : Type} {decode : F → Option ℝ}
    {mul sub div : Bounds F → Bounds F → Option (Bounds F)}
    (hm : OpSound decode mul (· * ·)) (hs : OpSound decode sub (· - ·))
    (hd : OpSound decode div (· / ·))
    {sin cos : Bounds F → Option (Bounds F)} (hsin : RangeSound decode sin)
    (hcos : ∀ I O x, cos I = some O → Contains decode I x → Contains decode O (Real.cos x))
    {two one : Bounds F} (ht : Contains decode two 2) (ho : Contains decode one 1)
    (depth : Nat) {I S C : Bounds F} {x : ℝ}
    (hr : run (m := Id) mul sub div sin cos two one depth I = some (S,C))
    (hx : Contains decode I x) : Contains decode S (Real.sin x) ∧ Contains decode C (Real.cos x) := by
  induction depth generalizing I S C x with
  | zero =>
    simp only [run,bind,pure] at hr
    split at hr <;> try contradiction
    next A ha =>
      split at hr <;> try contradiction
      next B hb =>
        cases hr
        exact ⟨hsin I _ x ha hx,hcos I _ x hb hx⟩
  | succ depth ih =>
    simp only [run,bind,pure] at hr
    split at hr <;> try contradiction
    next H hh =>
      split at hr <;> try contradiction
      next A B he =>
        obtain ⟨hS,hC⟩ := ih he (hd I two H x 2 hh hx ht)
        split at hr <;> try contradiction
        next TS hts =>
          split at hr <;> try contradiction
          next S2 hs2 =>
            split at hr <;> try contradiction
            next CC hcc =>
              split at hr <;> try contradiction
              next TCC htcc =>
                split at hr <;> try contradiction
                next C2 hc2 =>
                  cases hr
                  have hsin2 := hm TS B _ _ _ hs2 (hm two A TS _ _ hts ht hS) hC
                  have hcos2 := hs TCC one _ _ _ hc2 (hm two CC TCC _ _ htcc ht
                    (hm B B CC _ _ hcc hC hC)) ho
                  have heq : 2*(x/2) = x := by ring
                  constructor
                  · simpa only [← Real.sin_two_mul,heq] using hsin2
                  · simpa only [← pow_two,← Real.cos_two_mul,heq] using hcos2

theorem sine_sound {F : Type} {decode : F → Option ℝ}
    {mul sub div : Bounds F → Bounds F → Option (Bounds F)}
    (hm : OpSound decode mul (· * ·)) (hs : OpSound decode sub (· - ·))
    (hd : OpSound decode div (· / ·))
    {sin cos : Bounds F → Option (Bounds F)} (hsin : RangeSound decode sin)
    (hcos : ∀ I O x, cos I = some O → Contains decode I x → Contains decode O (Real.cos x))
    {two one : Bounds F} (ht : Contains decode two 2) (ho : Contains decode one 1)
    (depth : Nat) : RangeSound decode (sine (m := Id) mul sub div sin cos two one depth) := by
  intro I O x hr hx
  simp only [sine,bind,pure] at hr
  split at hr <;> try contradiction
  next A B he =>
    cases hr
    exact (run_sound hm hs hd hsin hcos ht ho depth he hx).1

theorem cosine_sound {F : Type} {decode : F → Option ℝ}
    {mul sub div : Bounds F → Bounds F → Option (Bounds F)}
    (hm : OpSound decode mul (· * ·)) (hs : OpSound decode sub (· - ·))
    (hd : OpSound decode div (· / ·))
    {sin cos : Bounds F → Option (Bounds F)} (hsin : RangeSound decode sin)
    (hcos : ∀ I O x, cos I = some O → Contains decode I x → Contains decode O (Real.cos x))
    {two one : Bounds F} (ht : Contains decode two 2) (ho : Contains decode one 1)
    (depth : Nat) {I O : Bounds F} {x : ℝ}
    (hr : cosine (m := Id) mul sub div sin cos two one depth I = some O)
    (hx : Contains decode I x) : Contains decode O (Real.cos x) := by
  simp only [cosine,bind,pure] at hr
  split at hr <;> try contradiction
  next A B he =>
    cases hr
    exact (run_sound hm hs hd hsin hcos ht ho depth he hx).2

theorem refine_sound {F : Type} {decode : F → Option ℝ}
    {old new : Bounds F → Option (Bounds F)} (ho : RangeSound decode old)
    (hn : RangeSound decode new) {lt : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hmin : HardwareMultiplication.SelectSound decode mn min)
    (hmax : HardwareMultiplication.SelectSound decode mx max) :
    RangeSound decode (refine (m := Id) old new lt mn mx) := by
  intro I O x hr hx
  simp only [refine,bind,pure] at hr
  split at hr <;> try contradiction
  next A ha =>
    split at hr
    · cases hr; exact ho I _ x ha hx
    next B hb =>
      obtain ⟨K,hK,hxK⟩ := HardwareQuadrants.clip_point hc hmin hmax
        (ho I A x ha hx) (hn I B x hb hx)
      rw [hr] at hK
      cases hK
      exact hxK

end GeneralizedIntervalArithmetic.HardwareHalving
