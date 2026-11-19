import LinearDivision
import Evaluator

namespace GeneralizedIntervalArithmetic.SplitQuotient

/-- Exhaustive sign split of existing partial quotient semantics. Both branches
retain the original operand witnesses and the explicit nonzero condition. -/
theorem sign_split {α : Type*} (A B : α → ℝ → Prop) (p : α) (z : ℝ) :
    QuotientValues A B p z ↔
      QuotientValues A (fun p y => B p y ∧ y < 0) p z ∨
      QuotientValues A (fun p y => B p y ∧ 0 < y) p z := by
  constructor
  · rintro ⟨x,y,hx,hy,hn,hz⟩
    rcases lt_or_gt_of_ne hn with hs | hs
    · exact Or.inl ⟨x,y,hx,⟨hy,hs⟩,hn,hz⟩
    · exact Or.inr ⟨x,y,hx,⟨hy,hs⟩,hn,hz⟩
  · rintro (⟨x,y,hx,hy,hn,hz⟩ | ⟨x,y,hx,hy,hn,hz⟩) <;>
      exact ⟨x,y,hx,hy.1,hn,hz⟩

/-- External restrictions commute with quotient formation at the SAME parameter. -/
theorem restrict_iff {α : Type*} (A B : α → ℝ → Prop) (D : α → Prop)
    (p : α) (z : ℝ) :
    QuotientValues (fun p x => D p ∧ A p x) (fun p y => D p ∧ B p y) p z ↔
      D p ∧ QuotientValues A B p z := by
  constructor
  · rintro ⟨x,y,hx,hy,hn,hz⟩
    exact ⟨hx.1,x,y,hx.2,hy.2,hn,hz⟩
  · rintro ⟨hd,x,y,hx,hy,hn,hz⟩
    exact ⟨x,y,⟨hd,hx⟩,⟨hd,hy⟩,hn,hz⟩

theorem zero_only_absent {α : Type*} {A B : α → ℝ → Prop} {p : α}
    (hz : ∀ y, B p y → y = 0) : ¬ ∃ z, QuotientValues A B p z := by
  rintro ⟨z,x,y,hx,hy,hn,_⟩
  exact hn (hz y hy)

/-- A proof-side union of unbounded real rays. No infinity is a semantic value. -/
def rays (a c d : ℝ) : Set ℝ := Set.Iic (-a/c) ∪ Set.Ici (a/d)

theorem negative_bound {a c x y : ℝ} (ha : 0 ≤ a) (hx : a ≤ x)
    (hy : -c ≤ y) (hs : y < 0) : x/y ≤ -a/c := by
  have h := div_le_div₀ (ha.trans hx) hx (neg_pos.mpr hs) (show -y ≤ c by linarith)
  simpa [div_neg,neg_div] using neg_le_neg h

theorem positive_bound {a d x y : ℝ} (ha : 0 ≤ a) (hx : a ≤ x)
    (hy : y ≤ d) (hs : 0 < y) : a/d ≤ x/y :=
  div_le_div₀ (ha.trans hx) hx hs hy

/-- Numerical enclosure of every defined quotient, including both sides of zero.
The range may be loose; no existence or exact-image claim is implied. -/
theorem quotient_rays {α : Type*} {A B : α → ℝ → Prop} {p : α}
    {a c d z : ℝ} (ha : 0 ≤ a) (_hc : 0 < c) (_hd : 0 < d)
    (hA : ∀ x, A p x → a ≤ x)
    (hB : ∀ y, B p y → -c ≤ y ∧ y ≤ d)
    (hz : QuotientValues A B p z) : z ∈ rays a c d := by
  rcases (sign_split A B p z).mp hz with
    ⟨x,y,hx,hy,_,rfl⟩ | ⟨x,y,hx,hy,_,rfl⟩
  · exact Or.inl (negative_bound ha (hA x hx) (hB y hy.1).1 hy.2)
  · exact Or.inr (positive_bound ha (hA x hx) (hB y hy.1).2 hy.2)

/-- The open central gap, not either closed ray endpoint, is excluded. -/
theorem gap_exclusion {α : Type*} {A B : α → ℝ → Prop} {p : α}
    {a c d z : ℝ} (ha : 0 ≤ a) (_hc : 0 < c) (_hd : 0 < d)
    (hA : ∀ x, A p x → a ≤ x)
    (hB : ∀ y, B p y → -c ≤ y ∧ y ≤ d)
    (hz : -a/c < z ∧ z < a/d) : ¬ QuotientValues A B p z := by
  intro hv
  rcases quotient_rays ha _hc _hd hA hB hv with h | h
  · exact (not_le_of_gt hz.1) h
  · exact (not_le_of_gt hz.2) h

/-- Existing expression semantics uses the same coordinate environment for both
operands; this bridge does not introduce an independently chosen input pair. -/
theorem expression_iff (u v : ℝ) (a b : Expr) (z : ℝ) :
    Value u v (.div a b) z ↔
    QuotientValues (fun (_ : Unit) x => Value u v a x)
      (fun _ y => Value u v b y) () z := by
  constructor
  · intro hz
    cases hz with
    | div hx hy hn => exact ⟨_,_,hx,hy,hn,rfl⟩
  · rintro ⟨x,y,hx,hy,hn,rfl⟩
    exact Value.div hx hy hn

theorem expression_rays {u v z a c d : ℝ} {e f : Expr} (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 < d)
    (he : ∀ x, Value u v e x → a ≤ x)
    (hf : ∀ y, Value u v f y → -c ≤ y ∧ y ≤ d)
    (hv : Value u v (.div e f) z) : z ∈ rays a c d :=
  quotient_rays (A := fun (_ : Unit) x => Value u v e x)
    (B := fun _ y => Value u v f y) ha hc hd he hf ((expression_iff u v e f z).mp hv)

/-- Exact image only for the full scalar input interval with zero removed.
The reverse implication constructs the input witness; arbitrary expressions
need not attain every point of these rays. -/
theorem reciprocal_image {l u z : ℝ} (hl : l < 0) (hu : 0 < u) :
    (∃ x, l ≤ x ∧ x ≤ u ∧ x ≠ 0 ∧ z = 1/x) ↔
      z ≤ 1/l ∨ 1/u ≤ z := by
  constructor
  · rintro ⟨x,hx,hy,hn,rfl⟩
    rcases lt_or_gt_of_ne hn with hs | hs
    · have hb := negative_bound (a := (1 : ℝ)) (c := -l) (x := 1)
        (by norm_num) le_rfl (by simpa using hx) hs
      exact Or.inl (by simpa using hb)
    · exact Or.inr (positive_bound (by norm_num) le_rfl hy hs)
  · intro hz
    rcases hz with hn | hp
    · have hzneg : z < 0 := hn.trans_lt (one_div_neg.mpr hl)
      have hm : 1 ≤ l*z := by simpa [mul_comm] using (le_div_iff_of_neg hl).mp hn
      refine ⟨1/z, (le_div_iff_of_neg hzneg).mpr hm, ?_,
        one_div_ne_zero (ne_of_lt hzneg), by simp⟩
      exact (le_of_lt (one_div_neg.mpr hzneg)).trans (le_of_lt hu)
    · have hzpos : 0 < z := (one_div_pos.mpr hu).trans_le hp
      have hm : 1 ≤ z*u := (div_le_iff₀ hu).mp hp
      refine ⟨1/z, (le_of_lt hl).trans (le_of_lt (one_div_pos.mpr hzpos)),
        (div_le_iff₀ hzpos).mpr (by nlinarith [hm]),
        one_div_ne_zero (ne_of_gt hzpos), by simp⟩

end GeneralizedIntervalArithmetic.SplitQuotient
