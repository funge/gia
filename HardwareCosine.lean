import CosineProgram
import CosineTaylor
import SineEndpoints

namespace GeneralizedIntervalArithmetic.HardwareCosine
open HardwareAddition HardwareSine

/-- The cap at 1 is justified even for intervals containing the interior maximum. -/
theorem cap_one {F : Type} {decode : F → Option ℝ} {mn : F → F → F}
    (hm : HardwareMultiplication.SelectSound decode mn min)
    {one : F} (ho : decode one = some 1) {I : Bounds F} {x : ℝ}
    (hx : Contains decode I (Real.cos x)) :
    Contains decode (⟨I.lo, mn I.hi one⟩ : Bounds F) (Real.cos x) := by
  rcases hx with ⟨a, b, ha, hb, hl, hu⟩
  exact ⟨a, min b 1, ha, hm _ _ _ _ hb ho, hl, le_min hu (Real.cos_le_one x)⟩

/-- Conditional soundness of the shared hardware cosine program. -/
theorem run_encloses {F : Type} {decode : F → Option ℝ}
    {supported : Bounds F → Bool}
    {add sub mul div : Bounds F → Bounds F → Option (Bounds F)}
    (ha : OpSound decode add (· + ·)) (hs : OpSound decode sub (· - ·))
    (hm : OpSound decode mul (· * ·)) (hd : OpSound decode div (· / ·))
    {mn : F → F → F} (hmin : HardwareMultiplication.SelectSound decode mn min)
    {zero one : F} (hz : decode zero = some 0) (ho : decode one = some 1)
    {two c24 c720 c40320 : Bounds F}
    (h2 : Contains decode two 2) (h24 : Contains decode c24 24)
    (h720 : Contains decode c720 720) (h40320 : Contains decode c40320 40320)
    {I O : Bounds F}
    (hg : supported I = true → ∀ x, Contains decode I x → -1 ≤ x ∧ x ≤ 1)
    (hr : run (m := Id) supported add sub mul div mn zero one two c24 c720 c40320 I = some O)
    {x : ℝ} (hx : Contains decode I x) : Contains decode O (Real.cos x) := by
  have hone : Contains decode (⟨one,one⟩ : Bounds F) 1 := ⟨1,1,ho,ho,le_rfl,le_rfl⟩
  unfold run at hr
  simp only [bind, pure] at hr
  split at hr
  · contradiction
  next h =>
    have hdom := hg (by simpa using h) x hx
    split at hr <;> try contradiction
    next x2 e2 =>
      have hx2 := hm _ _ _ _ _ e2 hx hx
      split at hr <;> try contradiction
      next x4 e4 =>
        have hx4 := hm _ _ _ _ _ e4 hx2 hx2
        split at hr <;> try contradiction
        next x6 e6 =>
          have hx6 := hm _ _ _ _ _ e6 hx4 hx2
          split at hr <;> try contradiction
          next x8 e8 =>
            have hx8 := hm _ _ _ _ _ e8 hx4 hx4
            split at hr <;> try contradiction
            next second es =>
              have hsecond := hd _ _ _ _ _ es hx2 h2
              split at hr <;> try contradiction
              next fourth ef =>
                have hfourth := hd _ _ _ _ _ ef hx4 h24
                split at hr <;> try contradiction
                next sixth et =>
                  have hsixth := hd _ _ _ _ _ et hx6 h720
                  split at hr <;> try contradiction
                  next error ee =>
                    have he := hd _ _ _ _ _ ee hx8 h40320
                    split at hr <;> try contradiction
                    next a ea =>
                      have haa := hs _ _ _ _ _ ea hone hsecond
                      split at hr <;> try contradiction
                      next b eb =>
                        have hbb := ha _ _ _ _ _ eb haa hfourth
                        split at hr <;> try contradiction
                        next p ep =>
                          have hpp := hs _ _ _ _ _ ep hbb hsixth
                          have hb := CosineTaylor.bounds hdom.1 hdom.2
                          have hpoly : Contains decode p (CosineTaylor.polynomial x) := by
                            convert hpp using 1
                            unfold CosineTaylor.polynomial
                            ring
                          have herr : Contains decode (⟨zero,error.hi⟩ : Bounds F)
                              (Real.cos x - CosineTaylor.polynomial x) := by
                            rcases he with ⟨l,u,_,hu,_,hupper⟩
                            refine ⟨0,u,hz,hu,sub_nonneg.mpr hb.1,?_⟩
                            have hid : (x*x*(x*x))*(x*x*(x*x))/40320 = x^8/40320 := by ring
                            dsimp at hupper
                            rw [hid] at hupper
                            linarith [hb.2]
                          split at hr <;> try contradiction
                          next result er =>
                            have hout := ha _ _ _ _ _ er hpoly herr
                            have hcos : Contains decode result (Real.cos x) := by simpa using hout
                            cases hr
                            exact cap_one hmin ho hcos

/-- The native [-1,1] guard discharges the range precondition. -/
theorem unit_run_sound {F : Type} {decode : F → Option ℝ}
    {lt : F → F → Bool} (hc : HardwareDivision.CompareSound decode lt)
    {add sub mul div : Bounds F → Bounds F → Option (Bounds F)}
    (ha : OpSound decode add (· + ·)) (hs : OpSound decode sub (· - ·))
    (hm : OpSound decode mul (· * ·)) (hd : OpSound decode div (· / ·))
    {mn : F → F → F} (hmin : HardwareMultiplication.SelectSound decode mn min)
    {zero negOne one : F} (hz : decode zero = some 0)
    (hn : decode negOne = some (-1)) (ho : decode one = some 1)
    {two c24 c720 c40320 : Bounds F}
    (h2 : Contains decode two 2) (h24 : Contains decode c24 24)
    (h720 : Contains decode c720 720) (h40320 : Contains decode c40320 40320) :
    ∀ I O x, run (m := Id) (unitGuard lt negOne one) add sub mul div mn zero one
      two c24 c720 c40320 I = some O → Contains decode I x → Contains decode O (Real.cos x) := by
  intro I O x hr hx
  apply run_encloses ha hs hm hd hmin hz ho h2 h24 h720 h40320 ?_ hr hx
  intro hg y hy
  rcases hy with ⟨a,b,ha,hb,hl,hu⟩
  obtain ⟨hl',hu'⟩ := signed_guard_sound hc hn ho ha hb hg
  exact ⟨hl'.trans hl,hu.trans hu'⟩

end GeneralizedIntervalArithmetic.HardwareCosine
