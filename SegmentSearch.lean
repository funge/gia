import PresenceChecker

namespace GeneralizedIntervalArithmetic

abbrev QPoint := ℚ × ℚ
abbrev SegmentCandidate := QPoint × QPoint

/-- Deterministic finite search: return the first certified candidate, not a
numerical root location. Failure says only that this list supplies no certificate. -/
def searchSegments (B : Backend) (X Y : QInterval) (e : Expr)
    (candidates : List SegmentCandidate) : Option SegmentCandidate :=
  candidates.find? (fun c => certifySegment B X Y e c.1 c.2)

theorem searchSegments_mem {B : Backend} {X Y : QInterval} {e : Expr}
    {cs : List SegmentCandidate} {c : SegmentCandidate}
    (h : searchSegments B X Y e cs = some c) : c ∈ cs :=
  List.mem_of_find?_eq_some h

theorem searchSegments_certified {B : Backend} {X Y : QInterval} {e : Expr}
    {cs : List SegmentCandidate} {c : SegmentCandidate}
    (h : searchSegments B X Y e cs = some c) : certifySegment B X Y e c.1 c.2 = true :=
  List.find?_some (p := fun c : SegmentCandidate => certifySegment B X Y e c.1 c.2) h

theorem searchSegments_sound {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {e : Expr} {cs : List SegmentCandidate} {c : SegmentCandidate}
    (h : searchSegments B X Y e cs = some c) :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y e 0 :=
  certifySegment_sound hB (searchSegments_certified h)

/-- Exact failure characterization, not a no-root theorem. -/
theorem searchSegments_none_iff (B : Backend) (X Y : QInterval) (e : Expr)
    (cs : List SegmentCandidate) :
    searchSegments B X Y e cs = none ↔
      ∀ c ∈ cs, certifySegment B X Y e c.1 c.2 = false := by
  simp [searchSegments, List.find?_eq_none]

/-- Complete relative to the supplied finite certificates, not to real roots. -/
theorem searchSegments_success_iff (B : Backend) (X Y : QInterval) (e : Expr)
    (cs : List SegmentCandidate) :
    (searchSegments B X Y e cs).isSome ↔
      ∃ c ∈ cs, certifySegment B X Y e c.1 c.2 = true := by
  simp [searchSegments, List.find?_isSome]

theorem searchSegments_append (B : Backend) (X Y : QInterval) (e : Expr)
    (as bs : List SegmentCandidate) :
    searchSegments B X Y e (as ++ bs) =
      (searchSegments B X Y e as).or (searchSegments B X Y e bs) := by
  simp [searchSegments, List.find?_append]

def classifyWithSearch (B : Backend) (X Y : QInterval) (e : Expr)
    (cs : List SegmentCandidate) : BoxResult :=
  if classifyExpr B X Y e = .empty then .empty
  else if (searchSegments B X Y e cs).isSome then .present else .unknown

theorem classifyWithSearch_empty {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {e : Expr} {cs : List SegmentCandidate}
    (h : classifyWithSearch B X Y e cs = .empty) :
    ¬ ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y e 0 := by
  unfold classifyWithSearch at h
  split at h
  · rename_i he
    exact eval_empty_pixel hB he
  · split at h <;> cases h

theorem classifyWithSearch_present {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {e : Expr} {cs : List SegmentCandidate}
    (h : classifyWithSearch B X Y e cs = .present) :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y e 0 := by
  unfold classifyWithSearch at h
  split at h
  · cases h
  · split at h
    · rename_i hs
      obtain ⟨c, _, hc⟩ := (searchSegments_success_iff B X Y e cs).mp hs
      exact certifySegment_sound hB hc
    · cases h

def QInterval.midpoint (I : QInterval) : ℚ := (I.lo + I.hi) / 2

theorem midpoint_bounds (I : QInterval) : I.lo ≤ I.midpoint ∧ I.midpoint ≤ I.hi := by
  have h2 : (0 : ℚ) < 2 := by norm_num
  constructor
  · apply (le_div_iff₀ h2).2
    calc I.lo * 2 = I.lo + I.lo := by ring
         _ ≤ I.lo + I.hi := add_le_add_left I.ordered I.lo
  · apply (div_le_iff₀ h2).2
    calc I.lo + I.hi ≤ I.hi + I.hi := add_le_add_right I.ordered I.hi
         _ = I.hi * 2 := by ring

def boxCenter (X Y : QInterval) : QPoint := (X.midpoint, Y.midpoint)

def boundarySamples (X Y : QInterval) : List QPoint :=
  [(X.lo, Y.lo), (X.lo, Y.hi), (X.hi, Y.lo), (X.hi, Y.hi),
   (X.midpoint, Y.lo), (X.midpoint, Y.hi), (X.lo, Y.midpoint), (X.hi, Y.midpoint)]

/-- An optional eight-segment policy. Degenerate boxes may produce duplicates.
Soundness is independent of this policy and does not imply completeness. -/
def boxSegments (X Y : QInterval) : List SegmentCandidate :=
  (boundarySamples X Y).map (fun p => (boxCenter X Y, p))

theorem boxCenter_inBox (X Y : QInterval) : inBox X Y (boxCenter X Y) :=
  ⟨(midpoint_bounds X).1, (midpoint_bounds X).2,
   (midpoint_bounds Y).1, (midpoint_bounds Y).2⟩

theorem boundarySamples_inBox {X Y : QInterval} {p : QPoint}
    (h : p ∈ boundarySamples X Y) : inBox X Y p := by
  have hx := X.ordered
  have hy := Y.ordered
  have mx := midpoint_bounds X
  have my := midpoint_bounds Y
  simp only [boundarySamples, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [inBox]

theorem boxSegments_inside {X Y : QInterval} {c : SegmentCandidate}
    (h : c ∈ boxSegments X Y) : inBox X Y c.1 ∧ inBox X Y c.2 := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact ⟨boxCenter_inBox X Y, boundarySamples_inBox hp⟩

theorem boxSegments_length (X Y : QInterval) : (boxSegments X Y).length = 8 := by
  simp [boxSegments, boundarySamples]

def classifyBox (B : Backend) (X Y : QInterval) (e : Expr) : BoxResult :=
  classifyWithSearch B X Y e (boxSegments X Y)

theorem classifyBox_empty {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {e : Expr} (h : classifyBox B X Y e = .empty) :
    ¬ ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y e 0 :=
  classifyWithSearch_empty hB h

theorem classifyBox_present {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {e : Expr} (h : classifyBox B X Y e = .present) :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y e 0 :=
  classifyWithSearch_present hB h

end GeneralizedIntervalArithmetic
