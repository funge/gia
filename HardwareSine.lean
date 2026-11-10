import SineProgram
import SineTaylor
import HardwareDivision
import HardwareSubtraction

namespace GeneralizedIntervalArithmetic.HardwareSine
open HardwareAddition

/-- Conditional interval-operation contract. It is discharged by the existing
assembly theorems from directed primitive contracts, not a new hardware axiom. -/
def OpSound {F : Type} (decode : F → Option ℝ)
    (op : Bounds F → Bounds F → Option (Bounds F)) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ I J O x y, op I J = some O → Contains decode I x → Contains decode J y →
    Contains decode O (f x y)

/-- The range guard is justified by the existing finite comparison contract. -/
theorem unitGuard_sound {F : Type} {decode : F → Option ℝ} {lt : F → F → Bool}
    (hc : HardwareDivision.CompareSound decode lt) {zero one : F}
    (hz : decode zero = some 0) (ho : decode one = some 1)
    {I : Bounds F} (hg : unitGuard lt zero one I = true)
    {x : ℝ} (hx : Contains decode I x) : 0 ≤ x ∧ x ≤ 1 := by
  rcases hx with ⟨a, b, ha, hb, hax, hxb⟩
  simp only [unitGuard, Bool.and_eq_true, Bool.not_eq_true'] at hg
  have hna : ¬ a < 0 := by
    intro h
    have := (hc _ _ _ _ ha hz).mpr h
    simp [hg.1.1] at this
  have hnb : ¬ 1 < b := by
    intro h
    have := (hc _ _ _ _ ho hb).mpr h
    simp [hg.1.2] at this
  exact ⟨(le_of_not_gt hna).trans hax, hxb.trans (le_of_not_gt hnb)⟩

/-- Existing primitive addition contracts discharge the interval contract. -/
theorem add_op_sound {F : Type} {decode : F → Option ℝ}
    {call : F → F → Option (F × F)}
    (hc : ∀ a b, HardwareAddition.CallSound decode a b (call a b)) :
    OpSound decode (fun I J => assemble (call I.lo J.lo) (call I.hi J.hi)) (· + ·) := by
  intro I J O x y hr hx hy
  exact HardwareAddition.assemble_encloses (hc _ _) (hc _ _) hr hx hy

theorem sub_op_sound {F : Type} {decode : F → Option ℝ}
    {call : F → F → Option (F × F)}
    (hc : ∀ a b, HardwareSubtraction.CallSound decode a b (call a b)) :
    OpSound decode (fun I J => assemble (call I.lo J.hi) (call I.hi J.lo)) (· - ·) := by
  intro I J O x y hr hx hy
  exact HardwareSubtraction.assemble_encloses (hc _ _) (hc _ _) hr hx hy

theorem mul_op_sound {F : Type} {decode : F → Option ℝ}
    {call : F → F → Option (F × F)} {mn mx : F → F → F}
    (hmin : HardwareMultiplication.SelectSound decode mn min)
    (hmax : HardwareMultiplication.SelectSound decode mx max)
    (hc : ∀ a b, HardwareMultiplication.CallSound decode a b (call a b)) :
    OpSound decode (fun I J => HardwareMultiplication.assembleFour mn mx
      (call I.lo J.lo) (call I.lo J.hi) (call I.hi J.lo) (call I.hi J.hi)) (· * ·) := by
  intro I J O x y hr hx hy
  exact HardwareMultiplication.assembleFour_encloses hmin hmax
    (hc _ _) (hc _ _) (hc _ _) (hc _ _) hr hx hy

theorem div_op_sound {F : Type} {decode : F → Option ℝ}
    {call : F → F → Option (F × F)} {mn mx : F → F → F} {lt : F → F → Bool}
    {zero : F} (hz : decode zero = some 0)
    (hcmp : HardwareDivision.CompareSound decode lt)
    (hmin : HardwareMultiplication.SelectSound decode mn min)
    (hmax : HardwareMultiplication.SelectSound decode mx max)
    (hc : ∀ a b, HardwareDivision.CallSound decode a b (call a b)) :
    OpSound decode (fun I J => HardwareDivision.assembleGuarded lt zero mn mx J
      (call I.lo J.lo) (call I.lo J.hi) (call I.hi J.lo) (call I.hi J.hi)) (· / ·) := by
  intro I J O x y hr hx hy
  exact (HardwareDivision.assembleGuarded_encloses hcmp hz hmin hmax
    (hc _ _) (hc _ _) (hc _ _) (hc _ _) hr hx hy).1

/-- The source-level pure specialization of the shared IO program is sound.
IO/FFI refinement and primitive behavior remain the explicit adapter boundary. -/
theorem run_encloses {F : Type} {decode : F → Option ℝ}
    {supported : Bounds F → Bool}
    {add sub mul div : Bounds F → Bounds F → Option (Bounds F)}
    (ha : OpSound decode add (· + ·)) (hs : OpSound decode sub (· - ·))
    (hm : OpSound decode mul (· * ·)) (hd : OpSound decode div (· / ·))
    {zero : F} (hz : decode zero = some 0)
    {six oneTwenty fiveThousandForty : Bounds F}
    (h6 : Contains decode six 6) (h120 : Contains decode oneTwenty 120)
    (h5040 : Contains decode fiveThousandForty 5040)
    {I O : Bounds F}
    (hg : supported I = true → ∀ x, Contains decode I x → 0 ≤ x ∧ x ≤ 1)
    (hr : run (m := Id) supported add sub mul div zero six oneTwenty fiveThousandForty I = some O)
    {x : ℝ} (hx : Contains decode I x) : Contains decode O (Real.sin x) := by
  unfold run at hr
  simp only [Id.run, bind, pure] at hr
  split at hr
  · contradiction
  next h =>
    have hdom := hg (by simpa using h) x hx
    split at hr <;> try contradiction
    next x2 e2 =>
      have h2 := hm _ _ _ _ _ e2 hx hx
      split at hr <;> try contradiction
      next x3 e3 =>
        have h3 := hm _ _ _ _ _ e3 h2 hx
        split at hr <;> try contradiction
        next x5 e5 =>
          have h5 := hm _ _ _ _ _ e5 h3 h2
          split at hr <;> try contradiction
          next x7 e7 =>
            have h7 := hm _ _ _ _ _ e7 h5 h2
            split at hr <;> try contradiction
            next third et =>
              have ht := hd _ _ _ _ _ et h3 h6
              split at hr <;> try contradiction
              next fifth ef =>
                have hf := hd _ _ _ _ _ ef h5 h120
                split at hr <;> try contradiction
                next error ee =>
                  have he := hd _ _ _ _ _ ee h7 h5040
                  split at hr <;> try contradiction
                  next difference ed =>
                    have hdif := hs _ _ _ _ _ ed hx ht
                    split at hr <;> try contradiction
                    next polynomial ep =>
                      have hp := ha _ _ _ _ _ ep hdif hf
                      have hb := SineTaylor.bounds hdom.1 hdom.2
                      have hpoly : Contains decode polynomial (SineTaylor.polynomial x) := by
                        convert hp using 1
                        unfold SineTaylor.polynomial
                        ring
                      have herr : Contains decode ⟨zero, error.hi⟩
                          (SineTaylor.polynomial x - Real.sin x) := by
                        rcases he with ⟨l, u, _, hu, _, hupper⟩
                        refine ⟨0, u, hz, hu, sub_nonneg.mpr hb.2, ?_⟩
                        have hid : x*x*x*(x*x)*(x*x) / 5040 = x^7 / 5040 := by ring
                        dsimp at hupper
                        rw [hid] at hupper
                        linarith [hb.1]
                      have hout := hs _ _ _ _ _ hr hpoly herr
                      simpa using hout

/-- Same-witness relational lifting preserves arbitrary external domains/holes. -/
def SinValues {α W : Type} (R : α → W → ℝ → Prop) (p : α) (w : W) (z : ℝ) : Prop :=
  ∃ x, R p w x ∧ z = Real.sin x

theorem sinValues_defined_iff {α W : Type} {R : α → W → ℝ → Prop} {p : α} {w : W} :
    (∃ z, SinValues R p w z) ↔ ∃ x, R p w x := by
  constructor
  · rintro ⟨_, x, hx, _⟩; exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩; exact ⟨Real.sin x, x, hx, rfl⟩

/-- Lift a pointwise enclosure (in particular `run_encloses`) without changing
input witnesses or dropping the caller's domain predicate. -/
theorem sinValues_enclosed {F α W : Type} {decode : F → Option ℝ}
    {O : Bounds F} {R : α → W → ℝ → Prop} {p : α} {w : W} {z : ℝ}
    (h : ∀ x, R p w x → Contains decode O (Real.sin x))
    (hz : SinValues R p w z) : Contains decode O z := by
  rcases hz with ⟨x, hx, rfl⟩
  exact h x hx

end GeneralizedIntervalArithmetic.HardwareSine
