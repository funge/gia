import HardwareSine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace GeneralizedIntervalArithmetic.HardwareSine
open HardwareAddition

/-- Sine is increasing throughout the supported domain, including zero. -/
theorem sin_monotone : MonotoneOn Real.sin (Set.Icc (-1 : ℝ) 1) := by
  intro a ha b hb hab
  exact Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.two_le_pi, ha.1]) (by linarith [Real.two_le_pi, hb.2]) hab

/-- The ideal endpoint Taylor enclosure, before hardware rounding. -/
theorem ideal_endpoint_bounds {a b x : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hx : a ≤ x ∧ x ≤ b) :
    SineTaylor.polynomial a - a^7/5040 ≤ Real.sin x ∧
    Real.sin x ≤ SineTaylor.polynomial b := by
  have hab := hx.1.trans hx.2
  have hal := SineTaylor.bounds ha (hab.trans hb)
  have hbu := SineTaylor.bounds (ha.trans hab) hb
  have hm := sin_monotone
  exact ⟨hal.1.trans (hm ⟨by linarith, hab.trans hb⟩ ⟨by linarith, hx.2.trans hb⟩ hx.1),
    (hm ⟨by linarith, hx.2.trans hb⟩ ⟨by linarith, hb⟩ hx.2).trans hbu.2⟩

/-- Exact-real endpoint bounds improve the natural interval polynomial bounds.
This is not a universal ordering assertion about loosely rounded adapters. -/
theorem ideal_endpoint_improves_natural {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a - b^3/6 + a^5/120 - b^7/5040 ≤ SineTaylor.polynomial a - a^7/5040 ∧
    SineTaylor.polynomial b ≤ b - a^3/6 + b^5/120 := by
  have h3 := pow_le_pow_left₀ ha hab 3
  have h7 := pow_le_pow_left₀ ha hab 7
  unfold SineTaylor.polynomial
  constructor <;> linarith

/-- Successful positive evaluator result. The existing `run_encloses` discharges
this condition; failure outside its domain remains unconstrained. -/
def RangeSound {F : Type} (decode : F → Option ℝ)
    (positive : Bounds F → Option (Bounds F)) : Prop :=
  ∀ I O x, positive I = some O → Contains decode I x → Contains decode O (Real.sin x)

/-- Use exactly the existing positive Taylor program and primitive contracts. -/
theorem positive_run_sound {F : Type} {decode : F → Option ℝ}
    {lt : F → F → Bool} (hc : HardwareDivision.CompareSound decode lt)
    {zero one : F} (hz : decode zero = some 0) (ho : decode one = some 1)
    {add sub mul div : Bounds F → Bounds F → Option (Bounds F)}
    (ha : OpSound decode add (· + ·)) (hs : OpSound decode sub (· - ·))
    (hm : OpSound decode mul (· * ·)) (hd : OpSound decode div (· / ·))
    {six c e : Bounds F} (h6 : Contains decode six 6) (h120 : Contains decode c 120)
    (h5040 : Contains decode e 5040) :
    RangeSound decode (run (m := Id) (unitGuard lt zero one) add sub mul div zero six c e) := by
  intro I O x hr hx
  exact run_encloses ha hs hm hd hz h6 h120 h5040
    (fun hg _ hy => unitGuard_sound hc hz ho hg hy) hr hx

/-- Odd symmetry is mathematical. Both native reflections use the old subtraction
contract, so no exact hardware-negation hypothesis is introduced. -/
theorem signedPoint_encloses {F : Type} {decode : F → Option ℝ}
    {lt : F → F → Bool} {zero : F} (hz : decode zero = some 0)
    {sub : Bounds F → Bounds F → Option (Bounds F)} (hs : OpSound decode sub (· - ·))
    {positive : Bounds F → Option (Bounds F)} (hp : RangeSound decode positive)
    {a : F} {x : ℝ} (hx : decode a = some x) {O : Bounds F}
    (hr : signedPoint (m := Id) lt zero sub positive a = some O) :
    Contains decode O (Real.sin x) := by
  have hzero : Contains decode (⟨zero, zero⟩ : Bounds F) 0 := ⟨0, 0, hz, hz, le_rfl, le_rfl⟩
  have hpoint : Contains decode (⟨a, a⟩ : Bounds F) x := ⟨x, x, hx, hx, le_rfl, le_rfl⟩
  unfold signedPoint at hr
  simp only [bind, pure] at hr
  split at hr
  · split at hr <;> try contradiction
    next reflected he =>
      have hn := hs _ _ _ _ _ he hzero hpoint
      split at hr <;> try contradiction
      next result er =>
        have hv := hp _ _ _ er hn
        have hout := hs _ _ _ _ _ hr hzero hv
        simpa only [zero_sub, Real.sin_neg, neg_neg] using hout
  · exact hp _ _ _ hr hpoint

/-- The same runtime guard, now with endpoints -1 and 1, needs only finite ordering. -/
theorem signed_guard_sound {F : Type} {decode : F → Option ℝ} {lt : F → F → Bool}
    (hc : HardwareDivision.CompareSound decode lt) {negOne one : F}
    (hn : decode negOne = some (-1)) (ho : decode one = some 1)
    {I : Bounds F} {a b : ℝ} (ha : decode I.lo = some a) (hb : decode I.hi = some b)
    (hg : unitGuard lt negOne one I = true) : -1 ≤ a ∧ b ≤ 1 := by
  simp only [unitGuard, Bool.and_eq_true, Bool.not_eq_true'] at hg
  constructor
  · by_contra h
    have := (hc _ _ _ _ ha hn).mpr (lt_of_not_ge h)
    simp [hg.1.1] at this
  · by_contra h
    have := (hc _ _ _ _ ho hb).mpr (lt_of_not_ge h)
    simp [hg.1.2] at this

/-- Endpoint assembly encloses every point of the interval, not just its endpoints. -/
theorem endpoints_enclose {F : Type} {decode : F → Option ℝ}
    {supported : Bounds F → Bool} {point : F → Option (Bounds F)}
    (hp : ∀ a x O, decode a = some x → point a = some O → Contains decode O (Real.sin x))
    {I O : Bounds F}
    (hg : supported I = true → ∀ a b, decode I.lo = some a → decode I.hi = some b →
      -1 ≤ a ∧ b ≤ 1)
    (hr : endpoints (m := Id) supported point I = some O)
    {x : ℝ} (hx : Contains decode I x) : Contains decode O (Real.sin x) := by
  rcases hx with ⟨a, b, ha, hb, hax, hxb⟩
  unfold endpoints at hr
  simp only [bind, pure] at hr
  split at hr
  · contradiction
  next h =>
    have hdom := hg (by simpa using h) a b ha hb
    split at hr <;> try contradiction
    next lower hl =>
      split at hr <;> try contradiction
      next upper hu =>
        have he : O = ⟨lower.lo, upper.hi⟩ := (Option.some.inj hr).symm
        subst O
        rcases hp I.lo a lower ha hl with ⟨l, u, dl, _, hla, _⟩
        rcases hp I.hi b upper hb hu with ⟨v, w, _, dw, _, hbw⟩
        have hab := hax.trans hxb
        refine ⟨l, w, dl, dw, ?_, ?_⟩
        · exact hla.trans (sin_monotone ⟨hdom.1, hab.trans hdom.2⟩
            ⟨hdom.1.trans hax, hxb.trans hdom.2⟩ hax)
        · exact (sin_monotone ⟨hdom.1.trans hax, hxb.trans hdom.2⟩
            ⟨hdom.1.trans hab, hdom.2⟩ hxb).trans hbw

/-- Composed signed endpoint client: all assumptions are inherited from the
positive Taylor evaluator, directed subtraction and finite comparison. -/
theorem signed_endpoints_enclose {F : Type} {decode : F → Option ℝ}
    {lt : F → F → Bool} (hc : HardwareDivision.CompareSound decode lt)
    {zero negOne one : F} (hz : decode zero = some 0)
    (hn : decode negOne = some (-1)) (ho : decode one = some 1)
    {sub : Bounds F → Bounds F → Option (Bounds F)} (hs : OpSound decode sub (· - ·))
    {positive : Bounds F → Option (Bounds F)} (hp : RangeSound decode positive)
    {I O : Bounds F}
    (hr : endpoints (m := Id) (unitGuard lt negOne one)
      (signedPoint (m := Id) lt zero sub positive) I = some O)
    {x : ℝ} (hx : Contains decode I x) : Contains decode O (Real.sin x) := by
  exact endpoints_enclose (fun _ _ _ hx hr => signedPoint_encloses hz hs hp hx hr)
    (fun hg _ _ ha hb => signed_guard_sound hc hn ho ha hb hg) hr hx

end GeneralizedIntervalArithmetic.HardwareSine
