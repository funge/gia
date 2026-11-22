import HardwareDivision

namespace GeneralizedIntervalArithmetic.TwoCornerDivision

/-- Two *paired-bound* calls will suffice mathematically: these are real operand
pairs, not a native executor or two individual directed-rounding instructions. -/
abbrev Corners := (ℝ × ℝ) × (ℝ × ℝ)

noncomputable def positiveCorners (a b c d : ℝ) : Corners :=
  if 0 ≤ a then ((a,d),(b,c)) else
  if b ≤ 0 then ((a,c),(b,d)) else ((a,c),(b,c))

noncomputable def negativeCorners (a b c d : ℝ) : Corners :=
  if 0 ≤ a then ((b,d),(a,c)) else
  if b ≤ 0 then ((b,c),(a,d)) else ((b,d),(a,d))

/-- This proof-side selector explicitly rejects reversed intervals and any
closed denominator interval meeting zero. None is no supplied bound. -/
noncomputable def select (a b c d : ℝ) : Option Corners :=
  if a ≤ b ∧ c ≤ d then
    if 0 < c then some (positiveCorners a b c d) else
    if d < 0 then some (negativeCorners a b c d) else none
  else none

def IsCorner (a b c d : ℝ) (p : ℝ × ℝ) : Prop :=
  (p.1 = a ∨ p.1 = b) ∧ (p.2 = c ∨ p.2 = d)

def Encloses (a b c d : ℝ) (p : Corners) : Prop :=
  ∀ x y, a ≤ x ∧ x ≤ b → c ≤ y ∧ y ≤ d →
    p.1.1 / p.1.2 ≤ x/y ∧ x/y ≤ p.2.1 / p.2.2

/-- First row, including a zero lower endpoint. -/
theorem positive_nonnegative {a b c d x y : ℝ}
    (ha : 0 ≤ a) (hc : 0 < c) (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    a/d ≤ x/y ∧ x/y ≤ b/c := by
  exact ⟨div_le_div₀ (ha.trans hx.1) hx.1 (hc.trans_le hy.1) hy.2,
    div_le_div₀ (ha.trans (hx.1.trans hx.2)) hx.2 hc hy.1⟩

/-- Second row; negating the numerator preserves the same witness. -/
theorem positive_nonpositive {a b c d x y : ℝ}
    (hb : b ≤ 0) (hc : 0 < c) (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    a/c ≤ x/y ∧ x/y ≤ b/d := by
  have h := positive_nonnegative (a := -b) (b := -a) (x := -x)
    (neg_nonneg.mpr hb) hc ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩ hy
  simp only [neg_div] at h
  exact ⟨neg_le_neg_iff.mp h.2, neg_le_neg_iff.mp h.1⟩

/-- Third row. Non-strict signs allow the shared zero boundary. -/
theorem positive_straddling {a b c d x y : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b) (hc : 0 < c)
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    a/c ≤ x/y ∧ x/y ≤ b/c := by
  have hl := positive_nonpositive (a := a) (b := a) (x := a) ha hc ⟨le_rfl,le_rfl⟩ hy
  have hu := positive_nonnegative (a := b) (b := b) (x := b) hb hc ⟨le_rfl,le_rfl⟩ hy
  exact ⟨hl.1.trans (div_le_div_of_nonneg_right hx.1 (hc.trans_le hy.1).le),
    (div_le_div_of_nonneg_right hx.2 (hc.trans_le hy.1).le).trans hu.2⟩

theorem negative_nonnegative {a b c d x y : ℝ}
    (ha : 0 ≤ a) (hd : d < 0) (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    b/d ≤ x/y ∧ x/y ≤ a/c := by
  have h := positive_nonpositive (a := -b) (b := -a) (c := -d) (d := -c) (x := -x) (y := -y)
    (neg_nonpos.mpr ha) (neg_pos.mpr hd) ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩
    ⟨neg_le_neg hy.2,neg_le_neg hy.1⟩
  simpa only [neg_div_neg_eq] using h

theorem negative_nonpositive {a b c d x y : ℝ}
    (hb : b ≤ 0) (hd : d < 0) (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    b/c ≤ x/y ∧ x/y ≤ a/d := by
  have h := positive_nonnegative (a := -b) (b := -a) (c := -d) (d := -c) (x := -x) (y := -y)
    (neg_nonneg.mpr hb) (neg_pos.mpr hd) ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩
    ⟨neg_le_neg hy.2,neg_le_neg hy.1⟩
  simpa only [neg_div_neg_eq] using h

theorem negative_straddling {a b c d x y : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b) (hd : d < 0)
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    b/d ≤ x/y ∧ x/y ≤ a/d := by
  have h := positive_straddling (a := -b) (b := -a) (c := -d) (d := -c) (x := -x) (y := -y)
    (neg_nonpos.mpr hb) (neg_nonneg.mpr ha) (neg_pos.mpr hd)
    ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩ ⟨neg_le_neg hy.2,neg_le_neg hy.1⟩
  simpa only [neg_div_neg_eq] using h

theorem positive_spec {a b c d : ℝ} (hc : 0 < c) :
    IsCorner a b c d (positiveCorners a b c d).1 ∧
    IsCorner a b c d (positiveCorners a b c d).2 ∧ Encloses a b c d (positiveCorners a b c d) := by
  unfold positiveCorners
  split
  · rename_i ha
    exact ⟨by simp [IsCorner],by simp [IsCorner],fun _ _ hx hy => positive_nonnegative ha hc hx hy⟩
  · rename_i ha
    split
    · rename_i hb
      exact ⟨by simp [IsCorner],by simp [IsCorner],fun _ _ hx hy => positive_nonpositive hb hc hx hy⟩
    · rename_i hb
      exact ⟨by simp [IsCorner],by simp [IsCorner],fun _ _ hx hy =>
        positive_straddling (le_of_not_ge ha) (le_of_not_ge hb) hc hx hy⟩

theorem negative_spec {a b c d : ℝ} (hd : d < 0) :
    IsCorner a b c d (negativeCorners a b c d).1 ∧
    IsCorner a b c d (negativeCorners a b c d).2 ∧ Encloses a b c d (negativeCorners a b c d) := by
  unfold negativeCorners
  split
  · rename_i ha
    exact ⟨by simp [IsCorner],by simp [IsCorner],fun _ _ hx hy => negative_nonnegative ha hd hx hy⟩
  · rename_i ha
    split
    · rename_i hb
      exact ⟨by simp [IsCorner],by simp [IsCorner],fun _ _ hx hy => negative_nonpositive hb hd hx hy⟩
    · rename_i hb
      exact ⟨by simp [IsCorner],by simp [IsCorner],fun _ _ hx hy =>
        negative_straddling (le_of_not_ge ha) (le_of_not_ge hb) hd hx hy⟩

theorem select_spec {a b c d : ℝ} {p : Corners} (h : select a b c d = some p) :
    a ≤ b ∧ c ≤ d ∧ (0 < c ∨ d < 0) ∧
    IsCorner a b c d p.1 ∧ IsCorner a b c d p.2 ∧ Encloses a b c d p := by
  unfold select at h
  split at h
  · rename_i ho
    split at h
    · rename_i hc
      cases h
      exact ⟨ho.1,ho.2,Or.inl hc,positive_spec hc⟩
    · split at h
      · rename_i hd
        cases h
        exact ⟨ho.1,ho.2,Or.inr hd,negative_spec hd⟩
      · cases h
  · cases h

theorem select_available {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hg : 0 < c ∨ d < 0) : ∃ p, select a b c d = some p := by
  unfold select
  rw [if_pos (show a ≤ b ∧ c ≤ d from ⟨hab,hcd⟩)]
  split
  · exact ⟨_,rfl⟩
  · rename_i hn
    rw [if_pos (hg.resolve_left hn)]
    exact ⟨_,rfl⟩

theorem corner_mem {a b c d : ℝ} {p : ℝ × ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hp : IsCorner a b c d p) :
    (a ≤ p.1 ∧ p.1 ≤ b) ∧ (c ≤ p.2 ∧ p.2 ≤ d) := by
  rcases hp with ⟨ha | hb,hc | hd⟩ <;> simp_all

/-- Both selected values occur, with nonzero denominator witnesses. This is
stronger than enclosure, but does not assert any correlated expression's image. -/
theorem extrema_attained {a b c d : ℝ} {p : Corners} (h : select a b c d = some p) :
    (∃ x y, (a ≤ x ∧ x ≤ b) ∧ (c ≤ y ∧ y ≤ d) ∧ y ≠ 0 ∧ x/y = p.1.1/p.1.2) ∧
    (∃ x y, (a ≤ x ∧ x ≤ b) ∧ (c ≤ y ∧ y ≤ d) ∧ y ≠ 0 ∧ x/y = p.2.1/p.2.2) := by
  obtain ⟨hab,hcd,hg,hl,hu,_⟩ := select_spec h
  have hm := corner_mem hab hcd hl
  have hn := corner_mem hab hcd hu
  exact ⟨⟨p.1.1,p.1.2,hm.1,hm.2,HardwareDivision.guarded_nonzero hg.symm hm.2,rfl⟩,
    ⟨p.2.1,p.2.2,hn.1,hn.2,HardwareDivision.guarded_nonzero hg.symm hn.2,rfl⟩⟩

/-- Equality concerns exact real extrema, not rounded calls or their availability. -/
theorem four_corner_extrema {a b c d : ℝ} {p : Corners} (h : select a b c d = some p) :
    p.1.1/p.1.2 = min (min (a/c) (a/d)) (min (b/c) (b/d)) ∧
    p.2.1/p.2.2 = max (max (a/c) (a/d)) (max (b/c) (b/d)) := by
  obtain ⟨hab,hcd,hg,hl,hu,he⟩ := select_spec h
  have hll := he a c ⟨le_rfl,hab⟩ ⟨le_rfl,hcd⟩
  have hlh := he a d ⟨le_rfl,hab⟩ ⟨hcd,le_rfl⟩
  have hhl := he b c ⟨hab,le_rfl⟩ ⟨le_rfl,hcd⟩
  have hhh := he b d ⟨hab,le_rfl⟩ ⟨hcd,le_rfl⟩
  have hm := corner_mem hab hcd hl
  have hn := corner_mem hab hcd hu
  have fl := HardwareDivision.four_quotients hm.1 hm.2 hg.symm
  have fu := HardwareDivision.four_quotients hn.1 hn.2 hg.symm
  exact ⟨le_antisymm (le_min (le_min hll.1 hlh.1) (le_min hhl.1 hhh.1)) fl.1,
    le_antisymm fu.2 (max_le (max_le hll.2 hlh.2) (max_le hhl.2 hhh.2))⟩

/-- The existing comparison contract can discharge separation, but finite
endpoint decoding and both interval orders remain explicit obligations. -/
theorem available_from_guard {F : Type} {decode : F → Option ℝ}
    {lt : F → F → Bool} {zero : F} {I J : HardwareAddition.Bounds F}
    (hcmp : HardwareDivision.CompareSound decode lt) (hz : decode zero = some 0)
    {a b c d : ℝ} (_ha : decode I.lo = some a) (_hb : decode I.hi = some b)
    (hc : decode J.lo = some c) (hd : decode J.hi = some d)
    (hab : a ≤ b) (hcd : c ≤ d) (hg : HardwareDivision.awayZero lt zero J = true) :
    ∃ p, select a b c d = some p :=
  select_available hab hcd (HardwareDivision.awayZero_sound hcmp hz hc hd hg).symm

/-- Proof-side bridge only. Operands must decode to the selected corners;
no native sign selector or executor is introduced or verified here. -/
theorem assemble_selected_encloses {F : Type} {decode : F → Option ℝ}
    {a b c d : ℝ} {p : Corners} (hs : select a b c d = some p)
    {ln ld un ud : F} {lower upper : Option (F × F)} {R : HardwareAddition.Bounds F}
    (hln : decode ln = some p.1.1) (hld : decode ld = some p.1.2)
    (hun : decode un = some p.2.1) (hud : decode ud = some p.2.2)
    (hl : HardwareDivision.CallSound decode ln ld lower)
    (hu : HardwareDivision.CallSound decode un ud upper)
    (hr : HardwareAddition.assemble lower upper = some R)
    {x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    HardwareAddition.Contains decode R (x/y) ∧ y ≠ 0 := by
  obtain ⟨hab,hcd,hg,hpc,hqc,he⟩ := select_spec hs
  have hm := corner_mem hab hcd hpc
  have hn := corner_mem hab hcd hqc
  have hlv := hl _ _ hln hld (HardwareDivision.guarded_nonzero hg.symm hm.2)
  have huv := hu _ _ hun hud (HardwareDivision.guarded_nonzero hg.symm hn.2)
  refine ⟨?_,HardwareDivision.guarded_nonzero hg.symm hy⟩
  cases lower with
  | none => simp [HardwareAddition.assemble] at hr
  | some l =>
    cases upper with
    | none => simp [HardwareAddition.assemble] at hr
    | some u =>
      simp [HardwareAddition.assemble] at hr
      subst R
      obtain ⟨lo,_,hlo,_,hlo',_⟩ := hlv l rfl
      obtain ⟨_,hi,_,hhi,_,hhi'⟩ := huv u rfl
      exact ⟨lo,hi,hlo,hhi,hlo'.trans (he x y hx hy).1,(he x y hx hy).2.trans hhi'⟩

end GeneralizedIntervalArithmetic.TwoCornerDivision
