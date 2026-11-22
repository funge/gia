import Binary64
import HardwareAffine

namespace GeneralizedIntervalArithmetic.FiniteAffineDemotion
open HardwareAddition HardwareAffine HardwareIntervalOps

/-- Cold-path certificate check for supplied endpoint words, not a rounder. -/
def certify (I : LinearInterval) (H : Form Binary64.Word) : Option (Form Binary64.Word) := do
  let l0 ← Binary64.decode H.atZero.lo
  let u0 ← Binary64.decode H.atZero.hi
  let l1 ← Binary64.decode H.atOne.lo
  let u1 ← Binary64.decode H.atOne.hi
  if l0 ≤ I.lower.atZero ∧ I.upper.atZero ≤ u0 ∧
      l1 ≤ I.lower.atOne ∧ I.upper.atOne ≤ u1 then some H else none

/-- The four exact comparisons, with successful finite decoding. -/
theorem certify_spec {I : LinearInterval} {H O : Form Binary64.Word}
    (h : certify I H = some O) : O = H ∧ ∃ l0 u0 l1 u1 : ℚ,
      Binary64.decode H.atZero.lo = some l0 ∧ Binary64.decode H.atZero.hi = some u0 ∧
      Binary64.decode H.atOne.lo = some l1 ∧ Binary64.decode H.atOne.hi = some u1 ∧
      l0 ≤ I.lower.atZero ∧ I.upper.atZero ≤ u0 ∧
      l1 ≤ I.lower.atOne ∧ I.upper.atOne ≤ u1 := by
  unfold certify at h
  cases h0 : Binary64.decode H.atZero.lo <;> simp only [h0, bind, pure, Option.bind] at h
  · contradiction
  next l0 =>
    cases h1 : Binary64.decode H.atZero.hi <;> simp only [h1, bind, pure, Option.bind] at h
    · contradiction
    next u0 =>
      cases h2 : Binary64.decode H.atOne.lo <;> simp only [h2, bind, pure, Option.bind] at h
      · contradiction
      next l1 =>
        cases h3 : Binary64.decode H.atOne.hi <;> simp only [h3, bind, pure, Option.bind] at h
        · contradiction
        next u1 =>
          split_ifs at h with hc
          · cases h
            exact ⟨rfl, l0, u0, l1, u1, rfl, rfl, rfl, rfl, hc⟩

private theorem endpoint_contains {lo hi : Binary64.Word} {l u a b : ℚ}
    (hl : Binary64.decode lo = some l) (hu : Binary64.decode hi = some u)
    (hla : l ≤ a) (hab : a ≤ b) (hbu : b ≤ u) :
    HardwareAddition.Contains Binary64.real ⟨lo,hi⟩ (a:ℝ) ∧
    HardwareAddition.Contains Binary64.real ⟨lo,hi⟩ (b:ℝ) := by
  have hdl : Binary64.real lo = some (l:ℝ) := by simp [Binary64.real,hl]
  have hdu : Binary64.real hi = some (u:ℝ) := by simp [Binary64.real,hu]
  exact ⟨⟨l,u,hdl,hdu,by exact_mod_cast hla,by exact_mod_cast hab.trans hbu⟩,
    ⟨l,u,hdl,hdu,by exact_mod_cast hla.trans hab,by exact_mod_cast hbu⟩⟩

theorem certified_endpoints {I : LinearInterval} {H O : Form Binary64.Word}
    (h : certify I H = some O) :
    HardwareAddition.Contains Binary64.real O.atZero (I.lower.atZero:ℝ) ∧
    HardwareAddition.Contains Binary64.real O.atZero (I.upper.atZero:ℝ) ∧
    HardwareAddition.Contains Binary64.real O.atOne (I.lower.atOne:ℝ) ∧
    HardwareAddition.Contains Binary64.real O.atOne (I.upper.atOne:ℝ) := by
  obtain ⟨rfl,l0,u0,l1,u1,h0,h1,h2,h3,ha,hb,hc,hd⟩ := certify_spec h
  obtain ⟨ha0,hb0⟩ := endpoint_contains h0 h1 ha I.orderedZero hb
  obtain ⟨ha1,hb1⟩ := endpoint_contains h2 h3 hc I.orderedOne hd
  exact ⟨ha0,hb0,ha1,hb1⟩

/-- Ideal endpoint order supplies machine order without additional comparisons. -/
theorem certified_order {I : LinearInterval} {H O : Form Binary64.Word}
    (h : certify I H = some O) : ∃ l0 u0 l1 u1 : ℚ,
    Binary64.decode O.atZero.lo = some l0 ∧ Binary64.decode O.atZero.hi = some u0 ∧
    Binary64.decode O.atOne.lo = some l1 ∧ Binary64.decode O.atOne.hi = some u1 ∧
    l0 ≤ u0 ∧ l1 ≤ u1 := by
  obtain ⟨rfl,l0,u0,l1,u1,h0,h1,h2,h3,ha,hb,hc,hd⟩ := certify_spec h
  exact ⟨l0,u0,l1,u1,h0,h1,h2,h3,ha.trans (I.orderedZero.trans hb),
    hc.trans (I.orderedOne.trans hd)⟩

/-- Reuse the endpoint-to-family bridge; every ideal value keeps the same t. -/
theorem certified_enclosure {I : LinearInterval} {H O : Form Binary64.Word}
    (h : certify I H = some O) {t z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hz : I.Contains t z) : HardwareAffine.Contains Binary64.real O t z := by
  obtain ⟨ha,hb,hc,hd⟩ := certified_endpoints h
  exact linear_bridge I ha hb hc hd ht hz

/-- Pointwise noncollapse is nonempty meaning at EVERY parameter, not a hull test. -/
theorem certified_noncollapse {I : LinearInterval} {H O : Form Binary64.Word}
    (h : certify I H = some O) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃ z, HardwareAffine.Contains Binary64.real O t z :=
  ⟨I.lower.value t, certified_enclosure h ht ⟨le_rfl,linear_ordered I ht⟩⟩

/-- Outward evaluation of a stored form at a supplied parameter interval.
Every unavailable intermediate result fails closed. No native caller is wired. -/
def evaluate {F : Type}
    (sub mul add : Bounds F → Bounds F → Option (Bounds F))
    (one parameter : Bounds F) (H : Form F) : Option (Bounds F) := do
  let w ← sub one parameter
  let a ← mul w H.atZero
  let b ← mul parameter H.atOne
  add a b

/-- The same real parameter witness is used in both weights. This theorem even
holds outside [0,1]; the ideal-family bridge below requires that domain. -/
theorem evaluate_sound {F : Type} {decode : F → Option ℝ}
    {sub mul add : Bounds F → Bounds F → Option (Bounds F)}
    (hs : OpSound decode sub (· - ·)) (hm : OpSound decode mul (· * ·))
    (ha : OpSound decode add (· + ·)) {one parameter O : Bounds F} {H : Form F}
    (h1 : HardwareAddition.Contains decode one 1)
    {t z : ℝ} (ht : HardwareAddition.Contains decode parameter t)
    (hz : HardwareAffine.Contains decode H t z)
    (he : evaluate sub mul add one parameter H = some O) :
    HardwareAddition.Contains decode O z := by
  rcases hz with ⟨a,b,haz,hbo,rfl⟩
  unfold evaluate at he
  cases hw : sub one parameter <;> simp only [hw,bind,pure,Option.bind] at he
  · contradiction
  next W =>
    cases hu : mul W H.atZero <;> simp only [hu,bind,pure,Option.bind] at he
    · contradiction
    next A =>
      cases hv : mul parameter H.atOne <;> simp only [hv,bind,pure,Option.bind] at he
      · contradiction
      next B =>
        exact ha _ _ _ _ _ he (hm _ _ _ _ _ hu (hs _ _ _ _ _ hw h1 ht) haz)
          (hm _ _ _ _ _ hv ht hbo)

/-- Certified raw words and conditional outward operations compose, without a
native Float/Word correspondence or a claim that the operations must succeed. -/
theorem certified_evaluation
    {sub mul add : Bounds Binary64.Word → Bounds Binary64.Word → Option (Bounds Binary64.Word)}
    (hs : OpSound Binary64.real sub (· - ·)) (hm : OpSound Binary64.real mul (· * ·))
    (ha : OpSound Binary64.real add (· + ·))
    {I : LinearInterval} {H C : Form Binary64.Word} {one parameter O : Bounds Binary64.Word}
    (hc : certify I H = some C) (h1 : HardwareAddition.Contains Binary64.real one 1)
    {t z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hp : HardwareAddition.Contains Binary64.real parameter t) (hz : I.Contains t z)
    (he : evaluate sub mul add one parameter C = some O) :
    HardwareAddition.Contains Binary64.real O z :=
  evaluate_sound hs hm ha h1 hp (certified_enclosure hc ht hz) he

end GeneralizedIntervalArithmetic.FiniteAffineDemotion
