import HardwareMultiplication

namespace GeneralizedIntervalArithmetic.HardwareDivision
open HardwareAddition HardwareMultiplication

/-- Finite IEEE ordering agreement, now used to prove the strict zero guard.
No relation is asserted for undecodable exceptional values. -/
def CompareSound {F : Type} (decode : F → Option ℝ) (lt : F → F → Bool) : Prop :=
  ∀ a b x y, decode a = some x → decode b = some y → (lt a b = true ↔ x < y)

theorem awayZero_sound {F : Type} {decode : F → Option ℝ} {lt : F → F → Bool}
    (hcmp : CompareSound decode lt) {zero : F} (hz : decode zero = some 0)
    {J : Bounds F} {c d : ℝ} (hc : decode J.lo = some c) (hd : decode J.hi = some d)
    (hg : awayZero lt zero J = true) : d < 0 ∨ 0 < c := by
  simp only [awayZero, Bool.or_eq_true] at hg
  exact hg.elim (fun h => Or.inl ((hcmp _ _ _ _ hd hz).mp h))
    (fun h => Or.inr ((hcmp _ _ _ _ hz hc).mp h))

theorem guarded_nonzero {c d y : ℝ} (h : d < 0 ∨ 0 < c) (hy : c ≤ y ∧ y ≤ d) :
    y ≠ 0 := by
  rcases h with hn | hp
  · exact ne_of_lt (hy.2.trans_lt hn)
  · exact ne_of_gt (hp.trans_le hy.1)

theorem four_quotients {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d) (h : d < 0 ∨ 0 < c) :
    min (min (a/c) (a/d)) (min (b/c) (b/d)) ≤ x/y ∧
    x/y ≤ max (max (a/c) (a/d)) (max (b/c) (b/d)) := by
  have hi : d⁻¹ ≤ y⁻¹ ∧ y⁻¹ ≤ c⁻¹ := by
    rcases h with hn | hp
    · have yn := hy.2.trans_lt hn
      exact ⟨(inv_le_inv_of_neg hn yn).2 hy.2,
        (inv_le_inv_of_neg yn (hy.1.trans_lt yn)).2 hy.1⟩
    · exact ⟨inv_anti₀ (hp.trans_le hy.1) hy.2, inv_anti₀ hp hy.1⟩
  have hb := four_products hx hi
  simpa only [← div_eq_mul_inv, min_comm, max_comm] using hb

/-- Primitive division contract is used only at nonzero denominators. -/
def CallSound {F : Type} (decode : F → Option ℝ) (a b : F)
    (result : Option (F × F)) : Prop :=
  ∀ x y, decode a = some x → decode b = some y → y ≠ 0 → ResultSound decode result (x/y)

theorem assembleGuarded_encloses {F : Type} {decode : F → Option ℝ}
    {lt : F → F → Bool} {zero : F} {chooseMin chooseMax : F → F → F}
    (hcmp : CompareSound decode lt) (hz : decode zero = some 0)
    (hmin : SelectSound decode chooseMin min) (hmax : SelectSound decode chooseMax max)
    {I J R : Bounds F} {ll lh hl hh : Option (F × F)}
    (hll : CallSound decode I.lo J.lo ll) (hlh : CallSound decode I.lo J.hi lh)
    (hhl : CallSound decode I.hi J.lo hl) (hhh : CallSound decode I.hi J.hi hh)
    (hr : assembleGuarded lt zero chooseMin chooseMax J ll lh hl hh = some R)
    {x y : ℝ} (hx : Contains decode I x) (hy : Contains decode J y) :
    Contains decode R (x/y) ∧ y ≠ 0 := by
  rcases hx with ⟨a, b, ha, hb, hx⟩
  rcases hy with ⟨c, d, hc, hd, hy⟩
  unfold assembleGuarded at hr
  split at hr
  next hg =>
    have hg' := awayZero_sound hcmp hz hc hd hg
    have hcd := hy.1.trans hy.2
    have cn := guarded_nonzero hg' ⟨le_rfl, hcd⟩
    have dn := guarded_nonzero hg' ⟨hcd, le_rfl⟩
    exact ⟨assembleFour_encloses_values hmin hmax
      (hll a c ha hc cn) (hlh a d ha hd dn) (hhl b c hb hc cn) (hhh b d hb hd dn)
      (four_quotients hx hy hg') hr, guarded_nonzero hg' hy⟩
  next => simp at hr

end GeneralizedIntervalArithmetic.HardwareDivision
