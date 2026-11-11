import SineReductionProgram
import SineEndpoints
import PiBounds

namespace GeneralizedIntervalArithmetic.HardwareSine
open HardwareAddition

/-- Periodicity holds for any integer, independent of how a candidate was found. -/
theorem reduce_encloses {F : Type} {decode : F → Option ℝ}
    {mul sub : Bounds F → Bounds F → Option (Bounds F)}
    (hm : OpSound decode mul (· * ·)) (hs : OpSound decode sub (· - ·))
    {kernel : Bounds F → Option (Bounds F)} (hk : RangeSound decode kernel)
    {P C I O : Bounds F} (hp : Contains decode P Real.pi)
    {n : ℤ} (hc : Contains decode C ((n : ℝ) * 2))
    (hr : reduce (m := Id) mul sub kernel P C I = some O)
    {x : ℝ} (hx : Contains decode I x) : Contains decode O (Real.sin x) := by
  unfold reduce at hr
  simp only [bind, pure] at hr
  split at hr <;> try contradiction
  next shift he =>
    have hshift := hm _ _ _ _ _ he hc hp
    split at hr <;> try contradiction
    next residual er =>
      have hres := hs _ _ _ _ _ er hx hshift
      have hout := hk _ _ _ hr hres
      have hid : x - (n : ℝ) * 2 * Real.pi = x - (n : ℝ) * (2 * Real.pi) := by ring
      simpa only [hid, Real.sin_sub_int_mul_two_pi] using hout

/-- All candidates refer to whole periods, with one common real input witness. -/
def PeriodsSound {F : Type} (decode : F → Option ℝ) (cs : List (Bounds F)) : Prop :=
  ∀ c ∈ cs, ∃ n : ℤ, Contains decode c ((n : ℝ) * 2)

theorem searchPeriods_encloses {F : Type} {decode : F → Option ℝ}
    {mul sub : Bounds F → Bounds F → Option (Bounds F)}
    (hm : OpSound decode mul (· * ·)) (hs : OpSound decode sub (· - ·))
    {kernel : Bounds F → Option (Bounds F)} (hk : RangeSound decode kernel)
    {P I O : Bounds F} (hp : Contains decode P Real.pi)
    {cs : List (Bounds F)} (hc : PeriodsSound decode cs)
    (hr : searchPeriods (m := Id) mul sub kernel P I cs = some O)
    {x : ℝ} (hx : Contains decode I x) : Contains decode O (Real.sin x) := by
  induction cs with
  | nil => simp [searchPeriods] at hr
  | cons c cs ih =>
    simp only [searchPeriods, bind, pure] at hr
    split at hr
    next out he =>
      cases hr
      obtain ⟨n, hn⟩ := hc c (by simp)
      exact reduce_encloses hm hs hk hp hn he hx
    next he =>
      exact ih (fun c hm => hc c (by simp [hm])) hr

/-- The fixed executable candidate list is certified by ordinary literal decoding;
there is no native floor, fractional part or arbitrary integer conversion. -/
theorem periodCandidates_sound {F : Type} {decode : F → Option ℝ}
    {zero two negTwo four negFour : F}
    (h0 : decode zero = some 0) (h2 : decode two = some 2)
    (hn2 : decode negTwo = some (-2)) (h4 : decode four = some 4)
    (hn4 : decode negFour = some (-4)) :
    PeriodsSound decode (periodCandidates zero two negTwo four negFour) := by
  intro c hc
  simp only [periodCandidates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 0, 0, h0, h0, by norm_num, by norm_num⟩
  · exact ⟨1, 2, 2, h2, h2, by norm_num, by norm_num⟩
  · exact ⟨-1, -2, -2, hn2, hn2, by norm_num, by norm_num⟩
  · exact ⟨2, 4, 4, h4, h4, by norm_num, by norm_num⟩
  · exact ⟨-2, -4, -4, hn4, hn4, by norm_num, by norm_num⟩

/-- The existing signed endpoint implementation discharges the reduced-kernel
contract; no separately assumed sine accuracy is needed. -/
theorem signed_kernel_sound {F : Type} {decode : F → Option ℝ}
    {lt : F → F → Bool} (hc : HardwareDivision.CompareSound decode lt)
    {zero negOne one : F} (hz : decode zero = some 0)
    (hn : decode negOne = some (-1)) (ho : decode one = some 1)
    {sub : Bounds F → Bounds F → Option (Bounds F)} (hs : OpSound decode sub (· - ·))
    {positive : Bounds F → Option (Bounds F)} (hp : RangeSound decode positive) :
    RangeSound decode (endpoints (m := Id) (unitGuard lt negOne one)
      (signedPoint (m := Id) lt zero sub positive)) := by
  intro I O x hr hx
  exact signed_endpoints_enclose hc hz hn ho hs hp hr hx

/-- Global sine bounds are proved, not a transcendental adapter assumption. -/
theorem global_enclosure {F : Type} {decode : F → Option ℝ} {negOne one : F}
    (hn : decode negOne = some (-1)) (ho : decode one = some 1) (x : ℝ) :
    Contains decode (⟨negOne,one⟩ : Bounds F) (Real.sin x) :=
  ⟨-1,1,hn,ho,Real.neg_one_le_sin x,Real.sin_le_one x⟩

theorem globalFallback_sound {F : Type} {decode : F → Option ℝ}
    (supported : Bounds F → Bool) {search : Bounds F → Option (Bounds F)}
    (hs : RangeSound decode search) {negOne one : F}
    (hn : decode negOne = some (-1)) (ho : decode one = some 1) :
    RangeSound decode (globalFallback (m := Id) supported search negOne one) := by
  intro I O x hr hx
  unfold globalFallback at hr
  simp only [bind,pure] at hr
  split at hr
  · contradiction
  · split at hr
    next R he => cases hr; exact hs I _ x he hx
    next he => cases hr; exact global_enclosure hn ho x

/-- Unlike enclosure-only primitive contracts, the pure fallback wrapper has a
success guarantee whenever its input guard accepts. This is not an IO theorem. -/
theorem globalFallback_defined {F : Type} (supported : Bounds F → Bool)
    (search : Bounds F → Option (Bounds F)) (negOne one : F) (I : Bounds F)
    (hg : supported I = true) :
    ∃ O, globalFallback (m := Id) supported search negOne one I = some O := by
  simp only [globalFallback,hg,Bool.not_true, Bool.false_eq_true,if_false,bind,pure]
  cases search I <;> simp

end GeneralizedIntervalArithmetic.HardwareSine
