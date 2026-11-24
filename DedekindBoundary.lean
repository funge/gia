import ExactImageHull

/-! §2.15.1: positive rational cuts and the missing boundary convention.
No choice of distinct cut sets is silently made into equality of descriptions. -/
namespace GeneralizedIntervalArithmetic.DedekindBoundary

noncomputable def strict (r : ℝ) : Set ℚ := {q|0≤q ∧ (q:ℝ)<r}
noncomputable def closed (r : ℝ) : Set ℚ := {q|0≤q ∧ (q:ℝ)≤r}
noncomputable def values (C : Set ℚ) : Set ℝ := (fun q : ℚ=>(q:ℝ)) '' C

theorem strict_downward (r : ℝ) {q c : ℚ} (hc : c∈strict r) (hq : 0≤q) (hqc : q<c) :
    q∈strict r := ⟨hq,(show (q:ℝ)<c by exact_mod_cast hqc).trans hc.2⟩
theorem closed_downward (r : ℝ) {q c : ℚ} (hc : c∈closed r) (hq : 0≤q) (hqc : q<c) :
    q∈closed r := ⟨hq,(show (q:ℝ)<c by exact_mod_cast hqc).le.trans hc.2⟩

theorem strict_lub {r : ℝ} (hr : 0<r) : IsLUB (values (strict r)) r := by
  constructor
  · rintro x ⟨q,hq,rfl⟩; exact hq.2.le
  · intro u hu
    by_contra hn
    have hur : u<r := lt_of_not_ge hn
    have h0 : 0≤u := hu ⟨0,⟨le_rfl,by simpa using hr⟩,by norm_num⟩
    obtain ⟨q,huq,hqr⟩ := exists_rat_btwn hur
    have hq : q∈strict r := ⟨by exact_mod_cast (h0.trans huq.le),hqr⟩
    exact (not_le_of_gt huq) (hu ⟨q,hq,rfl⟩)

theorem closed_lub {r : ℝ} (hr : 0<r) : IsLUB (values (closed r)) r := by
  constructor
  · rintro x ⟨q,hq,rfl⟩; exact hq.2
  · intro u hu
    apply (strict_lub hr).2
    rintro x ⟨q,hq,rfl⟩
    exact hu ⟨q,⟨hq.1,hq.2.le⟩,rfl⟩

theorem same_supremum {r : ℝ} (hr : 0<r) :
    sSup (values (strict r)) = r ∧ sSup (values (closed r)) = r := by
  have hs : (values (strict r)).Nonempty := ⟨0,0,⟨le_rfl,by simpa using hr⟩,by norm_num⟩
  have hc : (values (closed r)).Nonempty := ⟨0,0,⟨le_rfl,by simpa using hr.le⟩,by norm_num⟩
  exact ⟨(strict_lub hr).csSup_eq hs,(closed_lub hr).csSup_eq hc⟩

/-- Every nonempty proper downward-closed nonnegative rational cut has a
nonnegative real least upper bound. Properness supplies an actual missing bound. -/
theorem proper_nonempty_lub (C : Set ℚ) (hne : C.Nonempty)
    (hpos : ∀ q∈C, 0≤q)
    (hdown : ∀ c∈C, ∀ q:ℚ, 0≤q → q<c → q∈C)
    (hproper : ∃ b:ℚ, 0≤b ∧ b∉C) :
    ∃ r:ℝ, 0≤r ∧ IsLUB (values C) r := by
  obtain ⟨b,hb,hn⟩ := hproper
  have hu : BddAbove (values C) := by
    refine ⟨(b:ℝ),?_⟩
    rintro x ⟨q,hq,rfl⟩
    have hqb : q≤b := by
      by_contra h
      exact hn (hdown q hq b hb (lt_of_not_ge h))
    change (q:ℝ) ≤ (b:ℝ)
    exact_mod_cast hqb
  have hv : (values C).Nonempty := hne.image _
  obtain ⟨q,hq⟩ := hne
  refine ⟨sSup (values C),?_,isLUB_csSup hv hu⟩
  exact (show (0:ℝ)≤q by exact_mod_cast hpos q hq).trans
    (le_csSup hu ⟨q,hq,rfl⟩)

/-- Downward closure alone does not select a unique rational-boundary description. -/
theorem distinct_rational_boundary (r : ℚ) (hr : 0<r) : strict (r:ℝ) ≠ closed (r:ℝ) := by
  intro h
  have hc : r∈closed (r:ℝ) := ⟨hr.le,le_rfl⟩
  rw [← h] at hc
  exact lt_irrefl _ hc.2

/-- At zero the strict positive-side cut is empty. In ℝ it has no least upper
bound, even though the library's totalized sSup of the empty set is zero. -/
theorem zero_boundary : strict 0 = ∅ ∧ closed 0 = {0} := by
  constructor
  · ext q
    simp only [strict,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false,not_and]
    intro h
    exact not_lt_of_ge (by exact_mod_cast h)
  · ext q
    simp only [closed,Set.mem_setOf_eq,Set.mem_singleton_iff]
    constructor
    · rintro ⟨h,k⟩
      exact le_antisymm (by exact_mod_cast k) h
    · rintro rfl; norm_num

theorem empty_no_real_lub : ¬ ∃ r : ℝ, IsLUB (values (strict 0)) r := by
  rw [zero_boundary.1]
  rintro ⟨r,hr⟩
  have h : r≤r-1 := hr.2 (by simp [values,upperBounds])
  linarith

end GeneralizedIntervalArithmetic.DedekindBoundary
