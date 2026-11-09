import PiecewiseSelection

namespace GeneralizedIntervalArithmetic

/-- A finite union of shared-parameter enclosures, with no existence claim. -/
abbrev FiniteLinearCover := List LinearInterval

def FiniteLinearCover.Covers (C : FiniteLinearCover) (R : ℝ → ℝ → Prop) : Prop :=
  ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z, R t z → ∃ I ∈ C, I.Contains t z

theorem cover_singleton {I : LinearInterval} {R : ℝ → ℝ → Prop}
    (h : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z, R t z → I.Contains t z) :
    FiniteLinearCover.Covers [I] R := by
  intro t ht z hz
  exact ⟨I, by simp, h t ht z hz⟩

theorem cover_of_domain_sound {I : LinearInterval} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} (h : (I.onDomain D).Sound R) :
    FiniteLinearCover.Covers [I] R :=
  cover_singleton (fun t _ z hz => h.1 t z hz)

def FiniteLinearCover.select : BranchDecision → FiniteLinearCover → FiniteLinearCover → FiniteLinearCover
  | .yes, A, _ => A
  | .no, _, B => B
  | .unknown, A, B => A ++ B

theorem cover_select {c : BranchDecision} {P : ℝ → Prop}
    {A B : FiniteLinearCover} {RA RB : ℝ → ℝ → Prop}
    (hc : BranchSound c P) (ha : A.Covers RA) (hb : B.Covers RB) :
    (FiniteLinearCover.select c A B).Covers (PiecewiseValues P RA RB) := by
  intro t ht z hz
  cases c with
  | yes =>
    rcases hz with ⟨_,hz⟩ | ⟨hp,_⟩
    · exact ha t ht z hz
    · exact (hp (hc t ht)).elim
  | no =>
    rcases hz with ⟨hp,_⟩ | ⟨_,hz⟩
    · exact (hc t ht hp).elim
    · exact hb t ht z hz
  | unknown =>
    rcases hz with ⟨_,hz⟩ | ⟨_,hz⟩
    · obtain ⟨I, hi, hz⟩ := ha t ht z hz
      exact ⟨I, List.mem_append_left _ hi, hz⟩
    · obtain ⟨I, hi, hz⟩ := hb t ht z hz
      exact ⟨I, List.mem_append_right _ hi, hz⟩

theorem cover_excludes_zero {C : FiniteLinearCover} {R : ℝ → ℝ → Prop}
    (h : C.Covers R) (ha : ∀ I ∈ C, I.hull.AwayZero)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : ¬ R t 0 := by
  intro hz
  obtain ⟨I, hi, hz⟩ := h t ht 0 hz
  exact awayZero_nonzero (ha I hi) (linear_hull_encloses ht hz) rfl

/-- All components must pass the existing reciprocal guard. Failure is unknown. -/
def FiniteLinearCover.recip? : FiniteLinearCover → Option FiniteLinearCover
  | [] => some []
  | I :: C => do
    let J ← I.recip?
    let D ← FiniteLinearCover.recip? C
    pure (J :: D)

theorem cover_recip_member {C D : FiniteLinearCover} (h : C.recip? = some D)
    {I : LinearInterval} (hi : I ∈ C) : ∃ J ∈ D, I.recip? = some J := by
  induction C generalizing D with
  | nil => simp at hi
  | cons K C ih =>
    cases hk : K.recip? with
    | none => simp [FiniteLinearCover.recip?, hk] at h
    | some L =>
      cases hc : FiniteLinearCover.recip? C with
      | none => simp [FiniteLinearCover.recip?, hk, hc] at h
      | some E =>
        have hd : L :: E = D := by simpa [FiniteLinearCover.recip?, hk, hc] using h
        subst D
        rcases List.mem_cons.mp hi with rfl | hi
        · exact ⟨L, by simp, hk⟩
        · obtain ⟨J, hj, hr⟩ := ih hc hi
          exact ⟨J, List.mem_cons_of_mem _ hj, hr⟩

theorem cover_recip_sound {C D : FiniteLinearCover} {R : ℝ → ℝ → Prop}
    (h : C.Covers R) (hr : C.recip? = some D) :
    D.Covers (QuotientValues (fun _ z => z = 1) R) := by
  rintro t ht z ⟨x, y, rfl, hy, _, rfl⟩
  obtain ⟨I, hi, hy⟩ := h t ht y hy
  obtain ⟨J, hj, hr⟩ := cover_recip_member hr hi
  exact ⟨J, hj, by simpa [one_div] using linear_recip_encloses hr ht hy⟩

/-- Bridge executable arithmetic results to finite union enclosures. -/
theorem cover_guarded {X Y I : LinearInterval} {x y : ℝ → ℝ} {e : Expr}
    (hx : ∀ t ∈ Set.Icc (0:ℝ) 1, X.Contains t (x t))
    (hy : ∀ t ∈ Set.Icc (0:ℝ) 1, Y.Contains t (y t))
    (hr : evalGuarded X Y e = some I) :
    FiniteLinearCover.Covers [I] (fun t z => Value (x t) (y t) e z) :=
  cover_singleton (fun t ht _ hz => evalGuarded_sound ht (hx t ht) (hy t ht) hz hr)

/-- Every finite family of rational affine bounds has uniform finite real bounds
on its unit parameters, independently of any domain or existence certificate. -/
theorem finite_cover_bounded (C : FiniteLinearCover) :
    ∃ l u : ℝ, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ I ∈ C, ∀ z,
      I.Contains t z → l ≤ z ∧ z ≤ u := by
  induction C with
  | nil => exact ⟨0,0,by simp⟩
  | cons I C ih =>
    obtain ⟨l,u,h⟩ := ih
    refine ⟨min (I.hull.lo:ℝ) l,max (I.hull.hi:ℝ) u,?_⟩
    intro t ht J hj z hz
    rcases List.mem_cons.mp hj with rfl | hj
    · have hb := linear_hull_encloses ht hz
      exact ⟨(min_le_left _ _).trans hb.1,hb.2.trans (le_max_left _ _)⟩
    · have hb := h t ht J hj z hz
      exact ⟨(min_le_right _ _).trans hb.1,hb.2.trans (le_max_right _ _)⟩

theorem covered_relation_bounded {C : FiniteLinearCover} {R : ℝ → ℝ → Prop}
    (h : C.Covers R) :
    ∃ l u : ℝ, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z, R t z → l ≤ z ∧ z ≤ u := by
  obtain ⟨l,u,hb⟩ := finite_cover_bounded C
  refine ⟨l,u,?_⟩
  intro t ht z hz
  obtain ⟨I,hi,hI⟩ := h t ht z hz
  exact hb t ht I hi z hI

/-- Unbounded actual values cannot be repaired by adding finitely many bounded
components. This is a representation limit, not a claim of undefinedness. -/
theorem no_finite_cover_of_unbounded_below {R : ℝ → ℝ → Prop}
    (hu : ∀ l : ℝ, ∃ t ∈ Set.Icc (0:ℝ) 1, ∃ z, R t z ∧ z < l)
    (C : FiniteLinearCover) : ¬ C.Covers R := by
  intro hc
  obtain ⟨l,_,hb⟩ := covered_relation_bounded hc
  obtain ⟨t,ht,z,hz,hl⟩ := hu l
  exact (not_lt_of_ge (hb t ht z hz).1) hl

end GeneralizedIntervalArithmetic
