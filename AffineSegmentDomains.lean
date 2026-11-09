import AffineDomainGuards
import PresenceChecker
import SemanticContinuity

namespace GeneralizedIntervalArithmetic

/-- Strict same-sign endpoint guards certify the entire closed segment. -/
def affineSegmentSafe (gs : List RationalAffineForm) (a b : ℚ × ℚ) : Bool :=
  gs.all fun g => decide ((0 < g.valueRat a ∧ 0 < g.valueRat b) ∨
    (g.valueRat a < 0 ∧ g.valueRat b < 0))

theorem affine_form_segment (g : RationalAffineForm) (a b : ℝ × ℝ) (t : ℝ) :
    g.value (segment a.1 b.1 t, segment a.2 b.2 t) =
      segment (g.value a) (g.value b) t := by
  simp only [RationalAffineForm.value, segment]
  ring

theorem affine_segment_defined {gs : List RationalAffineForm} {a b : ℚ × ℚ}
    (h : affineSegmentSafe gs a b = true) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃ z, Value (segment a.1 b.1 t) (segment a.2 b.2 t) (affineReciprocalSum gs) z := by
  apply (affine_sum_defined_iff gs (segment a.1 b.1 t, segment a.2 b.2 t)).mpr
  intro g hg
  have hs := (List.all_eq_true.mp h) g hg
  have hs' : (0 < g.value ((a.1:ℝ), (a.2:ℝ)) ∧ 0 < g.value ((b.1:ℝ), (b.2:ℝ))) ∨
      (g.value ((a.1:ℝ), (a.2:ℝ)) < 0 ∧ g.value ((b.1:ℝ), (b.2:ℝ)) < 0) := by
    rw [← affine_form_cast, ← affine_form_cast]
    exact_mod_cast (of_decide_eq_true hs)
  rw [affine_form_segment g ((a.1:ℝ), (a.2:ℝ)) ((b.1:ℝ), (b.2:ℝ)) t]
  rcases hs' with hp | hn
  · have h1 := mul_nonneg (sub_nonneg.mpr ht.2) (le_of_lt hp.1)
    have h2 := mul_nonneg ht.1 (le_of_lt hp.2)
    by_cases hzero : t = 0
    · simpa [hzero] using ne_of_gt hp.1
    · have := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm hzero)) hp.2
      unfold segment
      linarith
  · have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) (le_of_lt hn.1)
    by_cases hzero : t = 0
    · simpa [hzero] using ne_of_lt hn.1
    · have := mul_neg_of_pos_of_neg (lt_of_le_of_ne ht.1 (Ne.symm hzero)) hn.2
      unfold segment
      linarith

private theorem same_sign_of_segment_nonzero {u v : ℝ}
    (h : ∀ t ∈ Set.Icc (0:ℝ) 1, segment u v t ≠ 0) :
    (0 < u ∧ 0 < v) ∨ (u < 0 ∧ v < 0) := by
  have hu : u ≠ 0 := by simpa using h 0 (by norm_num)
  have hv : v ≠ 0 := by simpa using h 1 (by norm_num)
  rcases lt_or_gt_of_ne hu with hu | hu
  · rcases lt_or_gt_of_ne hv with hv | hv
    · exact Or.inr ⟨hu,hv⟩
    · obtain ⟨t,ht,hz⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1)
        (segment_continuous u v).continuousOn
        (show (0:ℝ) ∈ Set.Icc (segment u v 0) (segment u v 1) by simp; constructor <;> linarith)
      exact False.elim (h t ht hz)
  · rcases lt_or_gt_of_ne hv with hv | hv
    · obtain ⟨t,ht,hz⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1)
        (segment_continuous u v).continuousOn
        (show (0:ℝ) ∈ Set.Icc (segment u v 1) (segment u v 0) by simp; constructor <;> linarith)
      exact False.elim (h t ht hz)
    · exact Or.inl ⟨hu,hv⟩

/-- Complete only for the generated affine reciprocal sums on this closed
segment. No external-domain, range, or root-existence claim is made. -/
theorem affine_segment_safe_iff_defined (gs : List RationalAffineForm) (a b : ℚ × ℚ) :
    affineSegmentSafe gs a b = true ↔
      ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ z,
        Value (segment a.1 b.1 t) (segment a.2 b.2 t) (affineReciprocalSum gs) z := by
  constructor
  · exact fun h _ ht => affine_segment_defined h ht
  · intro hd
    apply List.all_eq_true.mpr
    intro g hg
    apply decide_eq_true
    have hn : ∀ t ∈ Set.Icc (0:ℝ) 1,
        segment (g.value ((a.1:ℝ),(a.2:ℝ))) (g.value ((b.1:ℝ),(b.2:ℝ))) t ≠ 0 := by
      intro t ht
      have h := (affine_sum_defined_iff gs
        (segment a.1 b.1 t, segment a.2 b.2 t)).mp (hd t ht) g hg
      rwa [affine_form_segment g ((a.1:ℝ),(a.2:ℝ)) ((b.1:ℝ),(b.2:ℝ)) t] at h
    have hs := same_sign_of_segment_nonzero hn
    rw [← affine_form_cast, ← affine_form_cast] at hs
    exact_mod_cast hs

/-- Failure of the domain-only test proves a hole somewhere, not absence of
values everywhere and not absence of roots. Numerical checker failure differs. -/
theorem affine_segment_unsafe_iff_hole (gs : List RationalAffineForm) (a b : ℚ × ℚ) :
    affineSegmentSafe gs a b = false ↔
      ∃ t ∈ Set.Icc (0:ℝ) 1, ¬ ∃ z,
        Value (segment a.1 b.1 t) (segment a.2 b.2 t) (affineReciprocalSum gs) z := by
  rw [Bool.eq_false_iff]
  change (¬ affineSegmentSafe gs a b = true) ↔ _
  rw [affine_segment_safe_iff_defined]
  simp only [not_forall, _root_.not_imp, exists_prop]

/-- Restricted definedness separates the external path obligation from the
complete arithmetic-domain test; neither can stand in for the other. -/
theorem affine_segment_domain_defined_iff (gs : List RationalAffineForm) (a b : ℚ × ℚ)
    (E : ℝ → ℝ → Prop) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, ∃ z,
      E (segment a.1 b.1 t) (segment a.2 b.2 t) ∧
      Value (segment a.1 b.1 t) (segment a.2 b.2 t) (affineReciprocalSum gs) z) ↔
    (∀ t ∈ Set.Icc (0:ℝ) 1, E (segment a.1 b.1 t) (segment a.2 b.2 t)) ∧
      affineSegmentSafe gs a b = true := by
  constructor
  · intro h
    constructor
    · intro t ht
      obtain ⟨_,hE,_⟩ := h t ht
      exact hE
    · apply (affine_segment_safe_iff_defined gs a b).mpr
      intro t ht
      obtain ⟨z,_,hv⟩ := h t ht
      exact ⟨z,hv⟩
  · rintro ⟨hE,hs⟩ t ht
    obtain ⟨z,hv⟩ := affine_segment_defined hs ht
    exact ⟨z,hE t ht,hv⟩

/-- Reuse the existing endpoint evaluator; replace only the whole-box domain
requirement with an exact affine guard certificate along this segment. -/
def certifyAffineSegment (B : Backend) (X Y : QInterval)
    (gs : List RationalAffineForm) (a b : ℚ × ℚ) : Bool :=
  if inBox X Y a ∧ inBox X Y b ∧ affineSegmentSafe gs a b = true then
    match eval B (.point a.1) (.point a.2) (affineReciprocalSum gs),
      eval B (.point b.1) (.point b.2) (affineReciprocalSum gs) with
    | some L, some U => decide (L.hi ≤ 0 ∧ 0 ≤ U.lo)
    | _, _ => false
  else false

/-- Retain the path parameter so callers can transport the actual root into
an external domain certified along the whole path. -/
theorem certifyAffineSegment_path_sound {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {gs : List RationalAffineForm} {a b : ℚ × ℚ}
    (h : certifyAffineSegment B X Y gs a b = true) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, X.Contains (segment a.1 b.1 t) ∧
      Y.Contains (segment a.2 b.2 t) ∧
      Value (segment a.1 b.1 t) (segment a.2 b.2 t) (affineReciprocalSum gs) 0 := by
  unfold certifyAffineSegment at h
  split at h
  · rename_i hi
    cases hl : eval B (.point a.1) (.point a.2) (affineReciprocalSum gs) with
    | none => simp [hl] at h
    | some L =>
      cases hu : eval B (.point b.1) (.point b.2) (affineReciprocalSum gs) with
      | none => simp [hl, hu] at h
      | some U =>
        simp only [hl, hu, decide_eq_true_eq] at h
        have hd := fun t ht => affine_segment_defined hi.2.2 (t := t) ht
        have hc := expr_continuousOn_of_defined
          (segment_continuous (a.1:ℝ) b.1).continuousOn
          (segment_continuous (a.2:ℝ) b.2).continuousOn (affineReciprocalSum gs) hd
        have hv : ∀ t ∈ Set.Icc (0:ℝ) 1, Value (segment a.1 b.1 t)
            (segment a.2 b.2 t) (affineReciprocalSum gs)
            ((affineReciprocalSum gs).realValue (segment a.1 b.1 t) (segment a.2 b.2 t)) := by
          intro t ht
          obtain ⟨z, hz⟩ := hd t ht
          exact value_eq_realValue hz ▸ hz
        obtain ⟨hax, hay⟩ := inBox_sound hi.1
        obtain ⟨hbx, hby⟩ := inBox_sound hi.2.1
        have hL := eval_sound hB (by simp [QInterval.Contains, QInterval.point])
          (by simp [QInterval.Contains, QInterval.point]) (hv 0 (by norm_num)) L hl
        have hU := eval_sound hB (by simp [QInterval.Contains, QInterval.point])
          (by simp [QInterval.Contains, QInterval.point]) (hv 1 (by norm_num)) U hu
        obtain ⟨t,ht,hz⟩ := certified_curve_zero hc hL hU h.1 h.2
        exact ⟨t,ht,segment_mem hax hbx ht,segment_mem hay hby ht,hz ▸ hv t ht⟩
  · simp at h

/-- Compatibility: the existing box-presence contract is unchanged. -/
theorem certifyAffineSegment_sound {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {gs : List RationalAffineForm} {a b : ℚ × ℚ}
    (h : certifyAffineSegment B X Y gs a b = true) :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y (affineReciprocalSum gs) 0 := by
  obtain ⟨t,_,hx,hy,hv⟩ := certifyAffineSegment_path_sound hB h
  exact ⟨_,_,hx,hy,hv⟩

/-- Endpoint membership in E is insufficient: the domain premise covers every
point of the certified path. This is a semantic bridge, not a domain solver. -/
theorem certifyAffineSegment_domain_sound {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {gs : List RationalAffineForm} {a b : ℚ × ℚ}
    {E : ℝ → ℝ → Prop}
    (hE : ∀ t ∈ Set.Icc (0:ℝ) 1, E (segment a.1 b.1 t) (segment a.2 b.2 t))
    (h : certifyAffineSegment B X Y gs a b = true) :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ E x y ∧ Value x y (affineReciprocalSum gs) 0 := by
  obtain ⟨t,ht,hx,hy,hv⟩ := certifyAffineSegment_path_sound hB h
  exact ⟨_,_,hx,hy,hE t ht,hv⟩

/-- A narrow extension of the existing checker, preserving its empty proof and
falling back to unknown when neither presence certificate succeeds. -/
def classifyAffineWithSegment (B : Backend) (X Y : QInterval)
    (gs : List RationalAffineForm) (a b : ℚ × ℚ) : BoxResult :=
  if certifyAffineSegment B X Y gs a b then .present
  else classifyWithSegment B X Y (affineReciprocalSum gs) a b

theorem classifyAffineWithSegment_present {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {gs : List RationalAffineForm} {a b : ℚ × ℚ}
    (h : classifyAffineWithSegment B X Y gs a b = .present) :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y (affineReciprocalSum gs) 0 := by
  unfold classifyAffineWithSegment at h
  split at h
  · rename_i hc
    exact certifyAffineSegment_sound hB hc
  · exact classifyWithSegment_present hB h

theorem classifyAffineWithSegment_empty {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {gs : List RationalAffineForm} {a b : ℚ × ℚ}
    (h : classifyAffineWithSegment B X Y gs a b = .empty) :
    ¬ ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y (affineReciprocalSum gs) 0 := by
  unfold classifyAffineWithSegment at h
  split at h
  · cases h
  · exact classifyWithSegment_empty hB h

/-- Absence transports to every external restriction, with no path premise. -/
theorem classifyAffineWithSegment_domain_empty {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {gs : List RationalAffineForm} {a b : ℚ × ℚ}
    (E : ℝ → ℝ → Prop)
    (h : classifyAffineWithSegment B X Y gs a b = .empty) :
    ¬ ∃ x y, X.Contains x ∧ Y.Contains y ∧ E x y ∧ Value x y (affineReciprocalSum gs) 0 := by
  rintro ⟨x,y,hx,hy,_,hv⟩
  exact classifyAffineWithSegment_empty hB h ⟨x,y,hx,hy,hv⟩

end GeneralizedIntervalArithmetic
