import QuadrantProgram
import HardwareSine

namespace GeneralizedIntervalArithmetic.HardwareQuadrants
open HardwareAddition

def Valid {F : Type} (decode : F → Option ℝ) (I : Bounds F) : Prop :=
  ∃ a b, decode I.lo = some a ∧ decode I.hi = some b

theorem valid_of_contains {F : Type} {decode : F → Option ℝ} {I : Bounds F} {x : ℝ}
    (h : Contains decode I x) : Valid decode I := by
  rcases h with ⟨a,b,ha,hb,_,_⟩; exact ⟨a,b,ha,hb⟩

theorem clip_point {F : Type} {decode : F → Option ℝ} {lt : F → F → Bool}
    {mn mx : F → F → F} (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {I J : Bounds F} {x : ℝ} (hi : Contains decode I x) (hj : Contains decode J x) :
    ∃ K, clip lt mn mx I J = some K ∧ Contains decode K x := by
  rcases hi with ⟨a,b,ha,hb,hl,hu⟩
  rcases hj with ⟨c,d,hc',hd,jl,ju⟩
  have hlo := hm _ _ _ _ ha hc'
  have hhi := hn _ _ _ _ hb hd
  have horder : max a c ≤ min b d := (max_le hl jl).trans (le_min hu ju)
  have hfalse : lt (mn I.hi J.hi) (mx I.lo J.lo) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact (not_lt_of_ge horder) ((hc _ _ _ _ hhi hlo).mp h)
  refine ⟨⟨mx I.lo J.lo,mn I.hi J.hi⟩, ?_, max a c, min b d, hlo, hhi,
    max_le hl jl, le_min hu ju⟩
  simp [clip,hfalse]

theorem clip_nonempty {F : Type} {decode : F → Option ℝ} {lt : F → F → Bool}
    {mn mx : F → F → F} (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {I J K : Bounds F} (hi : Valid decode I) (hj : Valid decode J)
    (hr : clip lt mn mx I J = some K) : ∃ x, Contains decode K x := by
  rcases hi with ⟨a,b,ha,hb⟩
  rcases hj with ⟨c,d,hc',hd⟩
  have hlo := hm _ _ _ _ ha hc'
  have hhi := hn _ _ _ _ hb hd
  simp only [clip] at hr
  split at hr
  · contradiction
  next hg =>
    cases hr
    have horder : max a c ≤ min b d := by
      by_contra h
      exact hg ((hc _ _ _ _ hhi hlo).mpr (lt_of_not_ge h))
    exact ⟨max a c, max a c, min b d, hlo,hhi,le_rfl,horder⟩

theorem hull_contains {F : Type} {decode : F → Option ℝ} {mn mx : F → F → F}
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {I J : Bounds F} (hi : Valid decode I) (hj : Valid decode J) {x : ℝ}
    (hx : Contains decode I x ∨ Contains decode J x) :
    Contains decode (hull mn mx I J) x := by
  rcases hi with ⟨a,b,ha,hb⟩
  rcases hj with ⟨c,d,hc,hd⟩
  refine ⟨min a c,max b d,hn _ _ _ _ ha hc,hm _ _ _ _ hb hd,?_,?_⟩
  · rcases hx with h | h
    · rcases h with ⟨l,u,hl,hu,hx,_⟩
      have : a = l := Option.some.inj (ha.symm.trans hl); subst l
      exact (min_le_left _ _).trans hx
    · rcases h with ⟨l,u,hl,hu,hx,_⟩
      have : c = l := Option.some.inj (hc.symm.trans hl); subst l
      exact (min_le_right _ _).trans hx
  · rcases hx with h | h
    · rcases h with ⟨l,u,hl,hu,_,hx⟩
      have : b = u := Option.some.inj (hb.symm.trans hu); subst u
      exact hx.trans (le_max_left _ _)
    · rcases h with ⟨l,u,hl,hu,_,hx⟩
      have : d = u := Option.some.inj (hd.symm.trans hu); subst u
      exact hx.trans (le_max_right _ _)

theorem hullList_spec {F : Type} {decode : F → Option ℝ} {mn mx : F → F → F}
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {xs : List (Bounds F)} (hv : ∀ I ∈ xs, Valid decode I) {O : Bounds F}
    (hr : hullList mn mx xs = some O) :
    Valid decode O ∧ ∀ I ∈ xs, ∀ x, Contains decode I x → Contains decode O x := by
  induction xs generalizing O with
  | nil => simp [hullList] at hr
  | cons I xs ih =>
    have hI := hv I (by simp)
    have htail : ∀ J ∈ xs, Valid decode J := fun J hj => hv J (by simp [hj])
    simp only [hullList] at hr
    split at hr
    next ht =>
      cases hr
      have hempty : xs = [] := by
        cases xs with
        | nil => rfl
        | cons J js => simp only [hullList] at ht; split at ht <;> contradiction
      subst xs
      exact ⟨hI, by intro J hj x hx; simp only [List.mem_singleton] at hj; subst J; exact hx⟩
    next J ht =>
      cases hr
      obtain ⟨hJ,hall⟩ := ih htail ht
      constructor
      · rcases hI with ⟨a,b,ha,hb⟩
        rcases hJ with ⟨c,d,hc,hd⟩
        exact ⟨min a c,max b d,hn _ _ _ _ ha hc,hm _ _ _ _ hb hd⟩
      · intro K hk x hx
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hull_contains hn hm hI hJ (Or.inl hx)
        · exact hull_contains hn hm hI hJ (Or.inr (hall K hk x hx))

/-- Successful evaluated pieces all have decoded finite endpoints. -/
theorem pieces_valid {F : Type} {decode : F → Option ℝ} {lt : F → F → Bool}
    {mn mx : F → F → F} (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {f : ℝ → ℝ} {eval : Cell F → Bounds F → Option (Bounds F)} {I : Bounds F}
    (hi : Valid decode I) {cs : List (Cell F)}
    (hv : ∀ c ∈ cs, Valid decode c.domain)
    (he : ∀ c ∈ cs, ∀ J O x, eval c J = some O → Contains decode J x → Contains decode O (f x))
    {outs : List (Bounds F)} (hr : pieces (m := Id) lt mn mx eval I cs = some outs) :
    ∀ O ∈ outs, Valid decode O := by
  induction cs generalizing outs with
  | nil =>
    simp only [pieces, pure] at hr
    cases hr
    simp
  | cons c cs ih =>
    have hvt : ∀ d ∈ cs, Valid decode d.domain := fun d hd => hv d (by simp [hd])
    have het : ∀ d ∈ cs, ∀ J O x, eval d J = some O → Contains decode J x → Contains decode O (f x) :=
      fun d hd => he d (by simp [hd])
    simp only [pieces,bind,pure] at hr
    split at hr
    next hclip => exact ih hvt het hr
    next J hclip =>
      split at hr <;> try contradiction
      next O ho =>
        obtain ⟨x,hx⟩ := clip_nonempty hc hn hm hi (hv c (by simp)) hclip
        have hO := valid_of_contains (he c (by simp) J O x ho hx)
        split at hr <;> try contradiction
        next rest ht =>
          cases hr
          intro K hk
          rcases List.mem_cons.mp hk with rfl | hk
          · exact hO
          · exact ih hvt het ht K hk

/-- No point in a covered input is lost by skipping disjoint intersections. -/
theorem pieces_covers {F : Type} {decode : F → Option ℝ} {lt : F → F → Bool}
    {mn mx : F → F → F} (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {f : ℝ → ℝ} {eval : Cell F → Bounds F → Option (Bounds F)}
    {I : Bounds F} {cs : List (Cell F)}
    (he : ∀ c ∈ cs, ∀ J O x, eval c J = some O → Contains decode J x → Contains decode O (f x))
    {outs : List (Bounds F)} (hr : pieces (m := Id) lt mn mx eval I cs = some outs)
    {x : ℝ} (hx : Contains decode I x) (hcover : ∃ c ∈ cs, Contains decode c.domain x) :
    ∃ O ∈ outs, Contains decode O (f x) := by
  induction cs generalizing outs with
  | nil => simp at hcover
  | cons c cs ih =>
    have het : ∀ d ∈ cs, ∀ J O x, eval d J = some O → Contains decode J x → Contains decode O (f x) :=
      fun d hd => he d (by simp [hd])
    simp only [pieces,bind,pure] at hr
    split at hr
    next hclip =>
      apply ih het hr
      obtain ⟨d,hd,hx'⟩ := hcover
      rcases List.mem_cons.mp hd with rfl | hd
      · obtain ⟨J,hJ,_⟩ := clip_point hc hn hm hx hx'
        rw [hclip] at hJ; contradiction
      · exact ⟨d,hd,hx'⟩
    next J hclip =>
      split at hr <;> try contradiction
      next O ho =>
        split at hr <;> try contradiction
        next rest ht =>
          cases hr
          obtain ⟨d,hd,hx'⟩ := hcover
          rcases List.mem_cons.mp hd with rfl | hd
          · obtain ⟨K,hK,hmem⟩ := clip_point hc hn hm hx hx'
            rw [hclip] at hK
            cases hK
            exact ⟨O,by simp,he d (by simp) J O x ho hmem⟩
          · obtain ⟨R,hR,hmem⟩ := ih het ht ⟨d,hd,hx'⟩
            exact ⟨R,by simp [hR],hmem⟩

/-- End-to-end enclosure for a certified cover. Failure is not interpreted as an
empty result; every intersecting cell must evaluate successfully. -/
theorem run_encloses {F : Type} {decode : F → Option ℝ} {lt : F → F → Bool}
    {mn mx : F → F → F} (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {f : ℝ → ℝ} {eval : Cell F → Bounds F → Option (Bounds F)}
    {I O : Bounds F} {cs : List (Cell F)} {supported : Bounds F → Bool}
    (hv : ∀ c ∈ cs, Valid decode c.domain)
    (he : ∀ c ∈ cs, ∀ J O x, eval c J = some O → Contains decode J x → Contains decode O (f x))
    (hcover : supported I = true → ∀ x, Contains decode I x → ∃ c ∈ cs, Contains decode c.domain x)
    (hr : run (m := Id) supported lt mn mx eval cs I = some O)
    {x : ℝ} (hx : Contains decode I x) : Contains decode O (f x) := by
  unfold run at hr
  simp only [bind,pure] at hr
  split at hr
  · contradiction
  next hg =>
    have hcovered := hcover (by simpa using hg) x hx
    split at hr <;> try contradiction
    next outs hout =>
      have hvalid := pieces_valid hc hn hm (valid_of_contains hx) hv he hout
      obtain ⟨R,hR,hmR⟩ := pieces_covers hc hn hm he hout hx hcovered
      exact (hullList_spec hn hm hvalid hr).2 R hR _ hmR

end GeneralizedIntervalArithmetic.HardwareQuadrants
