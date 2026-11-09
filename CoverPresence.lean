import ConditionalCovers
import ConditionalContinuity

namespace GeneralizedIntervalArithmetic

/-- Defined conditional values are unique, including the guard value. No
existence premise is inferred for an undefined guard or inactive branch. -/
theorem conditional_value_unique {x y z w : ℝ} {e : ConditionalExpr}
    (hz : ConditionalValue x y e z) (hw : ConditionalValue x y e w) : z = w := by
  induction hz generalizing w with
  | leaf hz =>
    cases hw with
    | leaf hw => exact (value_eq_realValue hz).trans (value_eq_realValue hw).symm
  | yes hg hlt _ ih =>
    cases hw with
    | yes hk _ hw => exact ih hw
    | no hk hge _ =>
      have he := (value_eq_realValue hg).trans (value_eq_realValue hk).symm
      exact (not_lt_of_ge hge (he ▸ hlt)).elim
  | no hg hge _ ih =>
    cases hw with
    | yes hk hlt _ =>
      have he := (value_eq_realValue hg).trans (value_eq_realValue hk).symm
      exact (not_lt_of_ge (he ▸ hge) hlt).elim
    | no _ _ hw => exact ih hw

/-- Domain restriction keeps finite ranges and restricts both domain directions. -/
theorem cover_domain_restrict {C : FiniteLinearCover} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} (h : C.SoundOn D R) (P : ℝ → Prop) :
    C.SoundOn (D.inter ⟨P,P,fun _ hp => hp⟩) (fun t z => P t ∧ R t z) := by
  refine ⟨fun t z hz => h.1 t z hz.2, ?_, ?_⟩
  · intro t z hz
    exact ⟨(h.2.1 t z hz.2).1,(h.2.1 t z hz.2).2,hz.1⟩
  · intro t ht
    obtain ⟨z,hz⟩ := h.2.2 t ⟨ht.1,ht.2.1⟩
    exact ⟨z,ht.2.2,hz⟩

/-- Endpoint signs of every retained component plus a continuous representative
and definite definedness on the entire path certify an actual relational zero.
Agreement alone does not fill holes in the relation's domain. -/
theorem cover_domain_presence {C : FiniteLinearCover} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} {g : ℝ → ℝ}
    (h : C.SoundOn D R)
    (hg : ContinuousOn g (Set.Icc (0:ℝ) 1))
    (ha : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z, R t z → z = g t)
    (hd : ∀ t ∈ Set.Icc (0:ℝ) 1, D.definite t)
    (hn : ∀ I ∈ C, I.upper.atZero ≤ 0)
    (hp : ∀ I ∈ C, 0 ≤ I.lower.atOne) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, R t 0 := by
  have h0 : (0:ℝ) ∈ Set.Icc 0 1 := by norm_num
  have h1 : (1:ℝ) ∈ Set.Icc 0 1 := by norm_num
  obtain ⟨z,hz⟩ := cover_domain_definite h h0 (hd 0 h0)
  obtain ⟨I,hi,hI⟩ := h.1 0 z hz
  have hn' : g 0 ≤ 0 := by
    have hb : z ≤ (I.upper.atZero:ℝ) := by simpa [QAffine.value] using hI.2
    rw [ha 0 h0 z hz] at hb
    exact hb.trans (by exact_mod_cast hn I hi)
  obtain ⟨w,hw⟩ := cover_domain_definite h h1 (hd 1 h1)
  obtain ⟨J,hj,hJ⟩ := h.1 1 w hw
  have hp' : 0 ≤ g 1 := by
    have hb : (J.lower.atOne:ℝ) ≤ w := by simpa [QAffine.value] using hJ.1
    rw [ha 1 h1 w hw] at hb
    exact (by exact_mod_cast hp J hj : (0:ℝ) ≤ J.lower.atOne).trans hb
  obtain ⟨t,ht,hzero⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hg ⟨hn',hp'⟩
  obtain ⟨v,hv⟩ := cover_domain_definite h ht (hd t ht)
  have he : v = 0 := (ha t ht v hv).trans hzero
  exact ⟨t,ht,he ▸ hv⟩

end GeneralizedIntervalArithmetic
