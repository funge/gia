import ConditionalCovers

namespace GeneralizedIntervalArithmetic

/-- Inclusion of represented values on the shared unit parameter range. It does
not compare or infer domains. -/
def FiniteLinearCover.IncludedIn (C F : FiniteLinearCover) : Prop :=
  ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
    (∃ I ∈ C, I.Contains t z) → ∃ J ∈ F, J.Contains t z

theorem cover_inclusion_refl (C : FiniteLinearCover) : C.IncludedIn C :=
  fun _ _ _ h => h

theorem cover_inclusion_trans {A B C : FiniteLinearCover}
    (hab : A.IncludedIn B) (hbc : B.IncludedIn C) : A.IncludedIn C :=
  fun t ht z hz => hbc t ht z (hab t ht z hz)

theorem cover_inclusion_covers {C F : FiniteLinearCover} {R : ℝ → ℝ → Prop}
    (h : C.Covers R) (hi : C.IncludedIn F) : F.Covers R :=
  fun t ht z hz => hi t ht z (h t ht z hz)

theorem cover_inclusion_domain_sound {C F : FiniteLinearCover} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} (h : C.SoundOn D R) (hi : C.IncludedIn F) : F.SoundOn D R :=
  ⟨fun t z hz => hi t (h.2.1 t z hz).1 z (h.1 t z hz),h.2⟩

/-- The singleton interface is exactly the existing linear partial enclosure. -/
theorem singleton_soundOn_iff {I : LinearInterval} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} :
    FiniteLinearCover.SoundOn [I] D R ↔ (I.onDomain D).Sound R := by
  constructor
  · intro h
    refine ⟨?_,h.2⟩
    intro t z hz
    obtain ⟨J,hj,hz⟩ := h.1 t z hz
    have he := List.mem_singleton.mp hj
    subst J
    exact hz
  · intro h
    exact ⟨fun t z hz => ⟨I,by simp,h.1 t z hz⟩,h.2⟩

/-- Join a nonempty list with an explicit first element. -/
def FiniteLinearCover.joinFrom (I : LinearInterval) : List LinearInterval → LinearInterval
  | [] => I
  | J :: C => I.join (FiniteLinearCover.joinFrom J C)

private theorem joinFrom_encloses {I J : LinearInterval} {C : List LinearInterval}
    {t z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hj : J ∈ I :: C) (hz : J.Contains t z) :
    (FiniteLinearCover.joinFrom I C).Contains t z := by
  induction C generalizing I with
  | nil =>
    have he := List.mem_singleton.mp hj
    subst J
    exact hz
  | cons K C ih =>
    rcases List.mem_cons.mp hj with rfl | hj
    · exact linear_join_left ht hz
    · exact linear_join_right ht (ih hj)

/-- Empty remains empty; nonempty covers become one enclosing linear interval. -/
def FiniteLinearCover.coalesce : FiniteLinearCover → FiniteLinearCover
  | [] => []
  | I :: C => [FiniteLinearCover.joinFrom I C]

theorem cover_coalesce_inclusion (C : FiniteLinearCover) : C.IncludedIn C.coalesce := by
  intro t ht z hz
  cases C with
  | nil => simp at hz
  | cons I C =>
    obtain ⟨J,hj,hz⟩ := hz
    exact ⟨FiniteLinearCover.joinFrom I C,by simp [FiniteLinearCover.coalesce],
      joinFrom_encloses ht hj hz⟩

theorem cover_coalesce_length (C : FiniteLinearCover) : C.coalesce.length ≤ 1 := by
  cases C <;> simp [FiniteLinearCover.coalesce]

theorem cover_coalesce_domain_sound {C : FiniteLinearCover} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} (h : C.SoundOn D R) : C.coalesce.SoundOn D R :=
  cover_inclusion_domain_sound h (cover_coalesce_inclusion C)

/-- Postprocessing output-size limit, not an evaluation work/memory bound.
Zero capacity rejects nonempty covers as unknown instead of deleting values. -/
def FiniteLinearCover.limit (n : ℕ) (C : FiniteLinearCover) : Option FiniteLinearCover :=
  if C.length ≤ n then some C else if n = 0 then none else some C.coalesce

theorem cover_limit_empty (n : ℕ) : FiniteLinearCover.limit n [] = some [] := by
  simp [FiniteLinearCover.limit]

theorem cover_limit_zero_nonempty (I : LinearInterval) (C : List LinearInterval) :
    FiniteLinearCover.limit 0 (I :: C) = none := by
  simp [FiniteLinearCover.limit]

theorem cover_limit_positive (C : FiniteLinearCover) {n : ℕ} (hn : 0 < n) :
    (C.limit n).isSome := by
  unfold FiniteLinearCover.limit
  split
  · rfl
  · simp [Nat.ne_of_gt hn]

theorem cover_limit_unchanged {C : FiniteLinearCover} {n : ℕ} (h : C.length ≤ n) :
    C.limit n = some C := by simp [FiniteLinearCover.limit,h]

theorem cover_limit_inclusion {C F : FiniteLinearCover} {n : ℕ}
    (h : C.limit n = some F) : C.IncludedIn F := by
  unfold FiniteLinearCover.limit at h
  split at h
  · cases Option.some.inj h
    exact cover_inclusion_refl C
  · split at h
    · cases h
    · cases Option.some.inj h
      exact cover_coalesce_inclusion C

theorem cover_limit_length {C F : FiniteLinearCover} {n : ℕ}
    (h : C.limit n = some F) : F.length ≤ n := by
  unfold FiniteLinearCover.limit at h
  split at h
  · rename_i hn
    cases Option.some.inj h
    exact hn
  · split at h
    · cases h
    · rename_i hn
      cases Option.some.inj h
      exact (cover_coalesce_length C).trans (by omega)

theorem cover_limit_domain_sound {C F : FiniteLinearCover} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} {n : ℕ} (h : C.SoundOn D R) (hl : C.limit n = some F) :
    F.SoundOn D R := cover_inclusion_domain_sound h (cover_limit_inclusion hl)

end GeneralizedIntervalArithmetic
