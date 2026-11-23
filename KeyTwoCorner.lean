import Binary64Key

namespace GeneralizedIntervalArithmetic.KeyTwoCorner
open HardwareAddition Binary64Key
set_option exponentiation.threshold 2048
abbrev Word := Nat
abbrev Requests := WordTwoCorner.Requests Word

def zeroKey : UInt64 := 0x8000000000000000

/-- Only keys are normalized. Returned operands are the original raw words. -/
def requests (I J : Bounds Word) : Option Requests := do
  let a ← checkedKey I.lo
  let b ← checkedKey I.hi
  let c ← checkedKey J.lo
  let d ← checkedKey J.hi
  if a ≤ b ∧ c ≤ d ∧ (zeroKey < c ∨ d < zeroKey) then
    if zeroKey < c then
      if zeroKey ≤ a then return ((I.lo,J.hi),(I.hi,J.lo))
      else if b ≤ zeroKey then return ((I.lo,J.lo),(I.hi,J.hi))
      else return ((I.lo,J.lo),(I.hi,J.lo))
    else
      if zeroKey ≤ a then return ((I.hi,J.hi),(I.lo,J.lo))
      else if b ≤ zeroKey then return ((I.hi,J.lo),(I.lo,J.hi))
      else return ((I.hi,J.hi),(I.lo,J.hi))
  else none

theorem checked_none {w : Word} (h : Binary64.decode w = none) : checkedKey w = none := by
  have hh := checkedKey_available w
  cases hk : checkedKey w <;> simp_all

theorem checked_some {w : Word} {q : ℚ} (h : Binary64.decode w = some q) :
    ∃ k, checkedKey w = some k ∧ k.toNat = key w := by
  have hf := (finite_iff w).mpr ⟨q,h⟩
  have hh := checkedKey_spec w
  rw [hf] at hh
  cases hk : checkedKey w <;> simp_all

theorem requests_eq (I J : Bounds Word) : requests I J = WordTwoCorner.requests I J := by
  cases ha : Binary64.decode I.lo with
  | none => simp [requests,checked_none ha,WordTwoCorner.requests,WordTwoCorner.validate,ha]
  | some a =>
    obtain ⟨ka,hka,eka⟩ := checked_some ha
    cases hb : Binary64.decode I.hi with
    | none => simp [requests,hka,checked_none hb,WordTwoCorner.requests,WordTwoCorner.validate,ha,hb]
    | some b =>
      obtain ⟨kb,hkb,ekb⟩ := checked_some hb
      cases hc : Binary64.decode J.lo with
      | none => simp [requests,hka,hkb,checked_none hc,WordTwoCorner.requests,WordTwoCorner.validate,ha,hb,hc]
      | some c =>
        obtain ⟨kc,hkc,ekc⟩ := checked_some hc
        cases hd : Binary64.decode J.hi with
        | none => simp [requests,hka,hkb,hkc,checked_none hd,WordTwoCorner.requests,WordTwoCorner.validate,ha,hb,hc,hd]
        | some d =>
          obtain ⟨kd,hkd,ekd⟩ := checked_some hd
          have hz : Binary64.decode 0 = some 0 := by norm_num [Binary64.decode,Binary64.exponent,Binary64.fraction,Binary64.sign]
          have ez : zeroKey.toNat = key 0 := by rfl
          have hab : ka ≤ kb ↔ a ≤ b := by
            rw [UInt64.le_iff_toNat_le,eka,ekb]; exact decoded_key_le ha hb
          have hcd : kc ≤ kd ↔ c ≤ d := by
            rw [UInt64.le_iff_toNat_le,ekc,ekd]; exact decoded_key_le hc hd
          have hzc : zeroKey < kc ↔ 0 < c := by
            rw [UInt64.lt_iff_toNat_lt,ez,ekc]; exact decoded_key_lt hz hc
          have hdz : kd < zeroKey ↔ d < 0 := by
            rw [UInt64.lt_iff_toNat_lt,ekd,ez]; exact decoded_key_lt hd hz
          have hza : zeroKey ≤ ka ↔ 0 ≤ a := by
            rw [UInt64.le_iff_toNat_le,ez,eka]; exact decoded_key_le hz ha
          have hbz : kb ≤ zeroKey ↔ b ≤ 0 := by
            rw [UInt64.le_iff_toNat_le,ekb,ez]; exact decoded_key_le hb hz
          simp only [requests,hka,hkb,hkc,hkd,WordTwoCorner.requests,
            WordTwoCorner.validate,ha,hb,hc,hd,bind,pure,Option.bind,hab,hcd,hzc,hdz,hza,hbz]
          by_cases hg : a ≤ b ∧ c ≤ d ∧ (0 < c ∨ d < 0)
          · simp only [if_pos hg]
            simp only [WordTwoCorner.pick]
            split_ifs <;> rfl
          · simp only [if_neg hg]

/-- Executable dispatch with the same explicit per-call trace as the reference. -/
def run (call : Word → Word → Option (Word × Word)) (I J : Bounds Word) :
    List (Word × Word) × Option (Bounds Word) :=
  match requests I J with
  | none => ([],none)
  | some p => match call p.1.1 p.1.2 with
    | none => ([p.1],none)
    | some lo => ([p.1,p.2],assemble (some lo) (call p.2.1 p.2.2))

theorem run_eq (call) (I J : Bounds Word) : run call I J = WordTwoCorner.run call I J := by
  simp only [run,WordTwoCorner.run,requests_eq]
  rfl

theorem rejected_no_calls (call) {I J : Bounds Word} (h : requests I J = none) :
    run call I J = ([],none) := by simp [run,h]

theorem run_sound {call : Word → Word → Option (Word × Word)} {I J O : Bounds Word}
    (hc : ∀ p, requests I J = some p →
      HardwareDivision.CallSound Binary64.real p.1.1 p.1.2 (call p.1.1 p.1.2) ∧
      HardwareDivision.CallSound Binary64.real p.2.1 p.2.2 (call p.2.1 p.2.2))
    (ho : (run call I J).2 = some O) {x y : ℝ}
    (hx : Contains Binary64.real I x) (hy : Contains Binary64.real J y) :
    Contains Binary64.real O (x/y) ∧ y ≠ 0 := by
  apply WordTwoCorner.run_sound ?_ (by simpa only [run_eq] using ho) hx hy
  intro p hp
  exact hc p ((requests_eq I J).trans hp)

theorem run_refines {call : Word → Word → Option (Word × Word)}
    {I J : Bounds Word} {p : Requests} (hp : requests I J = some p)
    {mn mx : Word → Word → Word}
    (hmin : HardwareMultiplication.SelectSound Binary64.real mn min)
    (hmax : HardwareMultiplication.SelectSound Binary64.real mx max)
    {ll lh hl hh lower upper : Option (Word × Word)} {old : Bounds Word}
    {v₁ v₂ v₃ v₄ : ℝ}
    (h₁ : HardwareMultiplication.ResultSound Binary64.real ll v₁)
    (h₂ : HardwareMultiplication.ResultSound Binary64.real lh v₂)
    (h₃ : HardwareMultiplication.ResultSound Binary64.real hl v₃)
    (h₄ : HardwareMultiplication.ResultSound Binary64.real hh v₄)
    (hL : (p.1,lower) ∈ TwoCornerRefinement.observations I J ll lh hl hh)
    (hU : (p.2,upper) ∈ TwoCornerRefinement.observations I J ll lh hl hh)
    (hD : TwoCornerRefinement.downValue Binary64.real (call p.1.1 p.1.2) =
      TwoCornerRefinement.downValue Binary64.real lower)
    (hUp : TwoCornerRefinement.upValue Binary64.real (call p.2.1 p.2.2) =
      TwoCornerRefinement.upValue Binary64.real upper)
    (hold : HardwareMultiplication.assembleFour mn mx ll lh hl hh = some old) :
    ∃ new, (run call I J).2 = some new ∧ TwoCornerRefinement.Refines Binary64.real new old := by
  simpa only [run_eq] using WordTwoCorner.run_refines
    ((requests_eq I J).symm.trans hp) hmin hmax h₁ h₂ h₃ h₄ hL hU hD hUp hold

end GeneralizedIntervalArithmetic.KeyTwoCorner
