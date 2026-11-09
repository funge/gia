import AffineSegmentDomains

namespace GeneralizedIntervalArithmetic

/-- Finite conjunction of closed affine half-spaces, with a shared real point.
This denotes exactly the supplied constraints, not any additional external holes. -/
def affineRegion (cs : List RationalAffineForm) (x y : ℝ) : Prop :=
  ∀ g ∈ cs, 0 ≤ g.value (x,y)

/-- Yes means the entire path is included. No uses one uniformly violated
constraint. Unknown includes mixed paths and unresolved infeasible conjunctions. -/
def classifyAffineRegionSegment (cs : List RationalAffineForm) (a b : ℚ × ℚ) : BranchDecision :=
  if cs.all (fun g => decide (0 ≤ g.valueRat a ∧ 0 ≤ g.valueRat b)) then .yes
  else if cs.any (fun g => decide (g.valueRat a < 0 ∧ g.valueRat b < 0)) then .no
  else .unknown

private theorem region_endpoints_cast (cs : List RationalAffineForm) (a b : ℚ × ℚ) :
    cs.all (fun g => decide (0 ≤ g.valueRat a ∧ 0 ≤ g.valueRat b)) = true ↔
      affineRegion cs a.1 a.2 ∧ affineRegion cs b.1 b.2 := by
  simp only [List.all_eq_true, decide_eq_true_eq, affineRegion]
  constructor
  · intro h
    constructor <;> intro g hg
    · rw [← affine_form_cast]
      exact_mod_cast (h g hg).1
    · rw [← affine_form_cast]
      exact_mod_cast (h g hg).2
  · rintro ⟨ha,hb⟩ g hg
    have ha' := ha g hg
    have hb' := hb g hg
    rw [← affine_form_cast] at ha' hb'
    exact_mod_cast (And.intro ha' hb')

/-- Convexity proved directly for the supplied affine constraints. -/
theorem affine_region_segment {cs : List RationalAffineForm} {a b : ℝ × ℝ}
    (ha : affineRegion cs a.1 a.2) (hb : affineRegion cs b.1 b.2)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    affineRegion cs (segment a.1 b.1 t) (segment a.2 b.2 t) := by
  intro g hg
  rw [affine_form_segment g a b t]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (ha g hg))
    (mul_nonneg ht.1 (hb g hg))

theorem affine_region_query_yes_iff (cs : List RationalAffineForm) (a b : ℚ × ℚ) :
    classifyAffineRegionSegment cs a b = .yes ↔
      affineRegion cs a.1 a.2 ∧ affineRegion cs b.1 b.2 := by
  rw [← region_endpoints_cast]
  unfold classifyAffineRegionSegment
  split
  · simp_all
  · split <;> simp_all

/-- Reuse the existing whole-parameter BranchSound contract, not the point-query
interpretation of yes/no. No is only absence along this one path. -/
theorem affine_region_query_sound (cs : List RationalAffineForm) (a b : ℚ × ℚ) :
    BranchSound (classifyAffineRegionSegment cs a b)
      (fun t => affineRegion cs (segment a.1 b.1 t) (segment a.2 b.2 t)) := by
  unfold classifyAffineRegionSegment
  split
  · rename_i h
    obtain ⟨ha,hb⟩ := (region_endpoints_cast cs a b).mp h
    exact fun _ ht => affine_region_segment (a := ((a.1:ℝ),(a.2:ℝ)))
      (b := ((b.1:ℝ),(b.2:ℝ))) ha hb ht
  · split
    · rename_i h
      obtain ⟨g,hg,hv⟩ := List.any_eq_true.mp h
      have hv' : g.value ((a.1:ℝ),(a.2:ℝ)) < 0 ∧ g.value ((b.1:ℝ),(b.2:ℝ)) < 0 := by
        rw [← affine_form_cast, ← affine_form_cast]
        exact_mod_cast (of_decide_eq_true hv)
      intro t ht hE
      have hn := hE g hg
      rw [affine_form_segment g ((a.1:ℝ),(a.2:ℝ)) ((b.1:ℝ),(b.2:ℝ)) t] at hn
      by_cases hz : t = 0
      · simp only [hz,segment_zero] at hn
        exact (not_le_of_gt hv'.1) hn
      · have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) (le_of_lt hv'.1)
        have h2 := mul_neg_of_pos_of_neg (lt_of_le_of_ne ht.1 (Ne.symm hz)) hv'.2
        unfold segment at hn
        linarith
    · trivial

/-- Yes is complete for whole-path inclusion in this restricted convex class.
The no/unknown split is intentionally not a feasibility solver. -/
theorem affine_region_query_yes_iff_path (cs : List RationalAffineForm) (a b : ℚ × ℚ) :
    classifyAffineRegionSegment cs a b = .yes ↔
      ∀ t ∈ Set.Icc (0:ℝ) 1, affineRegion cs (segment a.1 b.1 t) (segment a.2 b.2 t) := by
  constructor
  · intro h
    have hs := affine_region_query_sound cs a b
    simpa [h,BranchSound] using hs
  · intro h
    apply (affine_region_query_yes_iff cs a b).mpr
    exact ⟨by simpa using h 0 (by norm_num), by simpa using h 1 (by norm_num)⟩

/-- The computed yes result discharges #55's whole-path external-domain premise.
Other restrictions need their own proof and must not be silently omitted. -/
theorem certifyAffineSegment_in_region {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {gs cs : List RationalAffineForm} {a b : ℚ × ℚ}
    (hR : classifyAffineRegionSegment cs a b = .yes)
    (h : certifyAffineSegment B X Y gs a b = true) :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ affineRegion cs x y ∧
      Value x y (affineReciprocalSum gs) 0 :=
  certifyAffineSegment_domain_sound hB ((affine_region_query_yes_iff_path cs a b).mp hR) h

end GeneralizedIntervalArithmetic
