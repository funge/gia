import SourceRoundedAlgebra
namespace GeneralizedIntervalArithmetic.NearestMinimizers
open DirectedOperationAlgebra SourceRoundedAlgebra FiniteFormat

/-- Mathematical nearest finite value, without selecting among minimizers. -/
def NearestReal (D : Finset ℚ) (x : ℝ) (q : ℚ) : Prop :=
  q∈D ∧ ∀r∈D, |x-(q:ℝ)|≤|x-(r:ℝ)|

theorem exists_iff (D : Finset ℚ) (x : ℝ) : (∃q,NearestReal D x q) ↔ D.Nonempty := by
  constructor
  · rintro ⟨q,hq,_⟩; exact ⟨q,hq⟩
  · intro h
    obtain ⟨q,hq,hm⟩ := D.exists_min_image (fun q => |x-(q:ℝ)|) h
    exact ⟨q,hq,hm⟩

theorem rational_agreement (D : Finset ℚ) (x q : ℚ) :
    NearestReal D x q ↔ SourceRoundedAlgebra.Nearest D x q := by
  unfold NearestReal SourceRoundedAlgebra.Nearest
  constructor
  · rintro ⟨hq,h⟩
    refine ⟨hq,?_⟩
    intro r hr
    exact_mod_cast h r hr
  · rintro ⟨hq,h⟩
    refine ⟨hq,?_⟩
    intro r hr
    exact_mod_cast h r hr

theorem in_range_exists {D : Finset ℚ} {x : ℝ} (h : InRange D x) : ∃q,NearestReal D x q := by
  obtain ⟨l,hl,_,_,_,_⟩ := h
  exact (exists_iff D x).2 ⟨l,hl⟩

theorem bracketed {D : Finset ℚ} {x : ℝ} {l u q : ℚ}
    (h : Rounded D x l u) (hq : NearestReal D x q) : l≤q ∧ q≤u := by
  have hs := rounded_sound h
  constructor
  · by_contra hn
    have hql : (q:ℝ)<l := by exact_mod_cast lt_of_not_ge hn
    have hh := hq.2 l h.1
    rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)] at hh
    linarith
  · by_contra hn
    have huq : (u:ℝ)<q := by exact_mod_cast lt_of_not_ge hn
    have hh := hq.2 u h.2.1
    rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)] at hh
    linarith

theorem unique_iff_strict {D : Finset ℚ} {x : ℝ} {q : ℚ} (h : NearestReal D x q) :
    (∀r,NearestReal D x r → r=q) ↔
      ∀r∈D,r≠q → |x-(q:ℝ)| < |x-(r:ℝ)| := by
  constructor
  · intro hu r hr hn
    apply lt_of_le_of_ne (h.2 r hr)
    intro he
    have hm : NearestReal D x r := ⟨hr,by intro s hs; rw [←he]; exact h.2 s hs⟩
    exact hn (hu r hm)
  · intro hs r hr
    by_contra hn
    exact (not_lt_of_ge (hr.2 q h.1)) (hs r hr.1 hn)

/-- Two distinct minimizers are precisely consecutive represented neighbors
with the input at their midpoint. No convention chooses either neighbor. -/
theorem tie_iff (D : Finset ℚ) (x : ℝ) (a b : ℚ) (hab : a<b) :
    (NearestReal D x a ∧ NearestReal D x b) ↔
      a∈D ∧ b∈D ∧ x=((a:ℝ)+b)/2 ∧ (∀q∈D,q≤a ∨ b≤q) := by
  have habr : (a:ℝ)<b := by exact_mod_cast hab
  constructor
  · rintro ⟨ha,hb⟩
    have he := le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)
    have hm : x=((a:ℝ)+b)/2 := by
      rcases abs_eq_abs.mp he with h | h <;> linarith
    refine ⟨ha.1,hb.1,hm,?_⟩
    intro q hq
    by_contra hn
    push_neg at hn
    have haq : (a:ℝ)<q := by exact_mod_cast hn.1
    have hqb : (q:ℝ)<b := by exact_mod_cast hn.2
    have hh := ha.2 q hq
    rw [abs_of_nonneg (by linarith)] at hh
    have hlt : |x-(q:ℝ)| < x-a := abs_lt.mpr ⟨by linarith,by linarith⟩
    linarith
  · rintro ⟨ha,hb,hm,hg⟩
    have he : |x-(a:ℝ)|=|x-(b:ℝ)| := by
      rw [abs_of_nonneg (by linarith),abs_of_nonpos (by linarith)]; linarith
    have hmin : NearestReal D x a := by
      refine ⟨ha,?_⟩
      intro q hq
      rw [abs_of_nonneg (by linarith)]
      rcases hg q hq with h | h
      · have hqa : (q:ℝ)≤a := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
      · have hbq : (b:ℝ)≤q := by exact_mod_cast h
        rw [abs_of_nonpos (by linarith)]; linarith
    exact ⟨hmin,⟨hb,by intro q hq; rw [←he]; exact hmin.2 q hq⟩⟩

theorem tied_only_two {D : Finset ℚ} {x : ℝ} {a b q : ℚ} (hab : a<b)
    (ha : NearestReal D x a) (hb : NearestReal D x b) (hq : NearestReal D x q) :
    q=a ∨ q=b := by
  have hm := ((tie_iff D x a b hab).1 ⟨ha,hb⟩).2.2.1
  have he := le_antisymm (hq.2 a ha.1) (ha.2 q hq.1)
  rcases abs_eq_abs.mp he with h | h
  · left; have : (q:ℝ)=a := by linarith
    exact_mod_cast this
  · right; have : (q:ℝ)=b := by linarith
    exact_mod_cast this

theorem nonunique_iff_midpoint_gap (D : Finset ℚ) (x : ℝ) (hne : D.Nonempty) :
    (¬ ∃!q,NearestReal D x q) ↔
      ∃a b : ℚ,a<b ∧ a∈D ∧ b∈D ∧ x=((a:ℝ)+b)/2 ∧ (∀q∈D,q≤a ∨ b≤q) := by
  constructor
  · intro hn
    obtain ⟨a,ha⟩ := (exists_iff D x).2 hne
    have hb : ∃b,NearestReal D x b ∧ b≠a := by
      by_contra h
      push_neg at h
      exact hn ⟨a,ha,h⟩
    obtain ⟨b,hb,hne⟩ := hb
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨b,a,h,(tie_iff D x b a h).1 ⟨hb,ha⟩⟩
    · exact ⟨a,b,h,(tie_iff D x a b h).1 ⟨ha,hb⟩⟩
  · rintro ⟨a,b,hab,h⟩ ⟨q,_,hu⟩
    have hh := (tie_iff D x a b hab).2 h
    have ha := hu a hh.1
    have hb := hu b hh.2
    exact (ne_of_lt hab) (ha.trans hb.symm)

theorem bracket_candidates {D : Finset ℚ} {x : ℝ} {l u q : ℚ}
    (h : Rounded D x l u) (hq : NearestReal D x q) : q=l ∨ q=u := by
  have hb := bracketed h hq
  have hs := (rounded_iff_extremal D x l u).1 h
  by_cases hx : (q:ℝ)≤x
  · exact Or.inl (le_antisymm (hs.2.2.2.2.1 q hq.1 hx) hb.1)
  · exact Or.inr (le_antisymm hb.2 (hs.2.2.2.2.2 q hq.1 (le_of_not_ge hx)))

theorem exact_unique {D : Finset ℚ} {q r : ℚ} (hq : q∈D) (h : NearestReal D q r) : r=q := by
  have hh := h.2 q hq
  simp only [sub_self,abs_zero] at hh
  have he := abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  have hr : (r:ℝ)=q := by linarith
  exact_mod_cast hr

/-- A small nonzero represented operand need not have a rounded finite
multiplicative inverse. This is not an overflow-result specification. -/
theorem small_product_no_one {D : Finset ℚ} {p : ℚ}
    (h0 : 0∈D) (he : (1/10:ℚ)∈D) (hp : p<1/10) (m : Mode) : ¬Rounds D m p 1 := by
  intro h
  cases m with
  | down =>
    obtain ⟨u,hu⟩ := h
    have hh := (rounded_sound hu).1
    have : (1:ℚ)≤p := by exact_mod_cast hh
    linarith
  | up =>
    obtain ⟨l,hl⟩ := h
    have hh := (rounded_iff_extremal D (p:ℝ) l 1).1 hl
    have hp' : (p:ℝ)≤((1/10:ℚ):ℝ) := by exact_mod_cast hp.le
    have := hh.2.2.2.2.2 (1/10) he hp'
    norm_num at this
  | nearest =>
    have hh := h.2 0 h0
    simp only [sub_zero] at hh
    rw [abs_of_nonpos (by linarith)] at hh
    rcases le_total 0 p with h | h
    · rw [abs_of_nonneg h] at hh; linarith
    · rw [abs_of_nonpos h] at hh; linarith

/-- One nonzero value belongs to both the literal and repaired decimal families. -/
def tiny : ℚ := 1/100000000000

theorem tiny_members : tiny∈values literal ∧ tiny∈values repairedIndex ∧ tiny≠0 := by
  constructor
  · convert literal_scaled 1 (-11) (by norm_num) using 1; norm_num [tiny]
  · constructor
    · convert repaired_scaled 1 (-11) (by norm_num) using 1; norm_num [tiny]
    · norm_num [tiny]

theorem literal_no_inverse (m : Mode) {q : ℚ} (hq : q∈values literal) :
    ¬Rounds (values literal) m (tiny*q) 1 := by
  have hb := FormatNormalization.literal_upper literal hq
  norm_num [literal] at hb
  have h0 : (0:ℚ)∈values literal := literal_constants (by simp)
  have he : (1/10:ℚ)∈values literal := by
    convert literal_scaled 1 (-1) (by norm_num) using 1; norm_num
  apply small_product_no_one h0 he _ m
  dsimp [tiny]
  linarith

theorem repaired_no_inverse (m : Mode) {q : ℚ} (hq : q∈values repairedIndex) :
    ¬Rounds (values repairedIndex) m (tiny*q) 1 := by
  have hb := FormatNormalization.literal_upper repairedIndex hq
  norm_num [repairedIndex] at hb
  have h0 : (0:ℚ)∈values repairedIndex := by
    convert repaired_scaled 0 0 (by norm_num) using 1; norm_num
  have he : (1/10:ℚ)∈values repairedIndex := by
    convert repaired_scaled 1 (-1) (by norm_num) using 1; norm_num
  apply small_product_no_one h0 he _ m
  dsimp [tiny]
  linarith

/-- An admitted small literal format: its nonzero values are units. -/
def unitFormat : Format := ⟨2,2,1,1,by decide,by decide,by decide⟩

theorem unit_format_values (q : ℚ) : q∈values unitFormat ↔ q= -1 ∨ q=0 ∨ q=1 := by
  rw [mem_values]
  constructor
  · rintro ⟨a,e,ha,hb,he,hf,hq⟩
    norm_num [unitFormat,bound,shift] at ha hb he hf
    have he0 : e=0 := by omega
    subst e
    have hc : a= -1 ∨ a=0 ∨ a=1 := by omega
    rcases hc with rfl | rfl | rfl <;> norm_num [value,unitFormat] at hq <;> simp [hq]
  · rintro (rfl | rfl | rfl)
    · exact ⟨-1,0,by norm_num [unitFormat,bound],by norm_num [unitFormat,bound],by norm_num [unitFormat,shift],by norm_num [unitFormat,shift],by norm_num [value,unitFormat]⟩
    · exact ⟨0,0,by norm_num [unitFormat,bound],by norm_num [unitFormat,bound],by norm_num [unitFormat,shift],by norm_num [unitFormat,shift],by norm_num [value,unitFormat]⟩
    · exact ⟨1,0,by norm_num [unitFormat,bound],by norm_num [unitFormat,bound],by norm_num [unitFormat,shift],by norm_num [unitFormat,shift],by norm_num [value,unitFormat]⟩

theorem unit_format_nonzero_inverses (m : Mode) {q : ℚ}
    (hq : q∈values unitFormat) (hn : q≠0) : Rounds (values unitFormat) m (q*q) 1 := by
  have h1 : (1:ℚ)∈values unitFormat := (unit_format_values 1).2 (by simp)
  rcases (unit_format_values q).1 hq with rfl | h | rfl
  · simpa using rounds_exact h1 m
  · exact (hn h).elim
  · simpa using rounds_exact h1 m

theorem zero_no_inverse {D : Finset ℚ} (h0 : 0∈D) (m : Mode) (q : ℚ) :
    ¬Rounds D m (0*q) 1 := by
  intro h
  have hh : Rounds D m 0 1 := by simpa using h
  have he := exact_forces h0 m hh
  norm_num at he

end GeneralizedIntervalArithmetic.NearestMinimizers
