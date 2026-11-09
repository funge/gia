import AffineRegions
import Subdivision

namespace GeneralizedIntervalArithmetic

/-- Check the existing region and arithmetic certificates, allowing either sign
orientation. The returned candidate need not encode the successful orientation. -/
def certifyAffineRegionCandidate (B : Backend) (X Y : QInterval)
    (gs cs : List RationalAffineForm) (c : SegmentCandidate) : Bool :=
  decide (classifyAffineRegionSegment cs c.1 c.2 = .yes) &&
    (certifyAffineSegment B X Y gs c.1 c.2 || certifyAffineSegment B X Y gs c.2 c.1)

theorem affine_region_candidate_sound {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {gs cs : List RationalAffineForm} {c : SegmentCandidate}
    (h : certifyAffineRegionCandidate B X Y gs cs c = true) :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ affineRegion cs x y ∧
      Value x y (affineReciprocalSum gs) 0 := by
  simp only [certifyAffineRegionCandidate, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true] at h
  rcases h.2 with hf | hr
  · exact certifyAffineSegment_in_region hB h.1 hf
  · have he := (affine_region_query_yes_iff cs c.1 c.2).mp h.1
    exact certifyAffineSegment_in_region hB
      ((affine_region_query_yes_iff cs c.2 c.1).mpr ⟨he.2,he.1⟩) hr

/-- Deterministic first-certificate search, reusing List.find? and existing
SegmentCandidate. None means only this supplied list yielded no certificate. -/
def searchAffineRegionSegments (B : Backend) (X Y : QInterval)
    (gs cs : List RationalAffineForm) (candidates : List SegmentCandidate) :
    Option SegmentCandidate :=
  candidates.find? (certifyAffineRegionCandidate B X Y gs cs)

theorem affine_region_search_mem {B : Backend} {X Y : QInterval}
    {gs cs : List RationalAffineForm} {candidates : List SegmentCandidate} {c : SegmentCandidate}
    (h : searchAffineRegionSegments B X Y gs cs candidates = some c) : c ∈ candidates :=
  List.mem_of_find?_eq_some h

theorem affine_region_search_sound {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {gs cs : List RationalAffineForm}
    {candidates : List SegmentCandidate} {c : SegmentCandidate}
    (h : searchAffineRegionSegments B X Y gs cs candidates = some c) :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ affineRegion cs x y ∧
      Value x y (affineReciprocalSum gs) 0 :=
  affine_region_candidate_sound hB (List.find?_some h)

theorem affine_region_search_none_iff (B : Backend) (X Y : QInterval)
    (gs cs : List RationalAffineForm) (candidates : List SegmentCandidate) :
    searchAffineRegionSegments B X Y gs cs candidates = none ↔
      ∀ c ∈ candidates, certifyAffineRegionCandidate B X Y gs cs c = false := by
  simp [searchAffineRegionSegments,List.find?_eq_none]

theorem affine_region_search_success_iff (B : Backend) (X Y : QInterval)
    (gs cs : List RationalAffineForm) (candidates : List SegmentCandidate) :
    (searchAffineRegionSegments B X Y gs cs candidates).isSome ↔
      ∃ c ∈ candidates, certifyAffineRegionCandidate B X Y gs cs c = true := by
  simp [searchAffineRegionSegments,List.find?_isSome]

/-- Only whole-box arithmetic zero exclusion can produce empty. Region query
no/unknown and finite search exhaustion cannot do so. -/
def classifyAffineRegionSearch (B : Backend) (X Y : QInterval)
    (gs cs : List RationalAffineForm) (candidates : List SegmentCandidate) : BoxResult :=
  if classifyExpr B X Y (affineReciprocalSum gs) = .empty then .empty
  else match searchAffineRegionSegments B X Y gs cs candidates with
    | some _ => .present
    | none => .unknown

theorem affine_region_search_result_sound {B : Backend} (hB : BackendSound B)
    (X Y : QInterval) (gs cs : List RationalAffineForm) (candidates : List SegmentCandidate) :
    ResultSound (classifyAffineRegionSearch B X Y gs cs candidates)
      (∃ x y, X.Contains x ∧ Y.Contains y ∧ affineRegion cs x y ∧
        Value x y (affineReciprocalSum gs) 0) := by
  unfold classifyAffineRegionSearch
  split
  · rename_i he
    constructor
    · intro _
      rintro ⟨x,y,hx,hy,_,hv⟩
      exact eval_empty_pixel hB he ⟨x,y,hx,hy,hv⟩
    · intro h
      cases h
  · cases hs : searchAffineRegionSegments B X Y gs cs candidates with
    | none => constructor <;> intro h <;> cases h
    | some c =>
      constructor
      · intro h
        cases h
      · intro _
        exact affine_region_search_sound hB hs

/-- Reuse the established eight center-to-boundary candidates. A center outside
the domain (or at a pole) can make every candidate fail despite a real root. -/
def classifyAffineRegionBox (B : Backend) (X Y : QInterval)
    (gs cs : List RationalAffineForm) : BoxResult :=
  classifyAffineRegionSearch B X Y gs cs (boxSegments X Y)

theorem affine_region_box_sound {B : Backend} (hB : BackendSound B)
    (X Y : QInterval) (gs cs : List RationalAffineForm) :
    ResultSound (classifyAffineRegionBox B X Y gs cs)
      (∃ x y, X.Contains x ∧ Y.Contains y ∧ affineRegion cs x y ∧
        Value x y (affineReciprocalSum gs) 0) :=
  affine_region_search_result_sound hB X Y gs cs (boxSegments X Y)

end GeneralizedIntervalArithmetic
