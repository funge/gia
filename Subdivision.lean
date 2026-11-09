import SegmentSearch

namespace GeneralizedIntervalArithmetic

def QInterval.lowerHalf (I : QInterval) : QInterval :=
  ⟨I.lo, I.midpoint, (midpoint_bounds I).1⟩
def QInterval.upperHalf (I : QInterval) : QInterval :=
  ⟨I.midpoint, I.hi, (midpoint_bounds I).2⟩

theorem lowerHalf_subset {I : QInterval} {x : ℝ}
    (h : I.lowerHalf.Contains x) : I.Contains x := by
  exact ⟨h.1, h.2.trans (by exact_mod_cast (midpoint_bounds I).2)⟩
theorem upperHalf_subset {I : QInterval} {x : ℝ}
    (h : I.upperHalf.Contains x) : I.Contains x := by
  have hl : (I.lo : ℝ) ≤ I.midpoint := by exact_mod_cast (midpoint_bounds I).1
  exact ⟨hl.trans h.1, h.2⟩

/-- Closed children cover the parent, including their shared boundary. -/
theorem split_cover (I : QInterval) (x : ℝ) :
    I.Contains x ↔ I.lowerHalf.Contains x ∨ I.upperHalf.Contains x := by
  constructor
  · intro h
    rcases le_total x (I.midpoint : ℝ) with hl | hr
    · exact Or.inl ⟨h.1, hl⟩
    · exact Or.inr ⟨hr, h.2⟩
  · intro h
    exact h.elim lowerHalf_subset upperHalf_subset

theorem split_boundary (I : QInterval) :
    I.lowerHalf.Contains I.midpoint ∧ I.upperHalf.Contains I.midpoint := by
  have hl : (I.lo : ℝ) ≤ I.midpoint := by exact_mod_cast (midpoint_bounds I).1
  have hu : (I.midpoint : ℝ) ≤ I.hi := by exact_mod_cast (midpoint_bounds I).2
  exact ⟨⟨hl, le_rfl⟩, ⟨le_rfl, hu⟩⟩

def HasRoot (X Y : QInterval) (e : Expr) : Prop :=
  ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y e 0

theorem hasRoot_split_x (X Y : QInterval) (e : Expr) :
    HasRoot X Y e ↔ HasRoot X.lowerHalf Y e ∨ HasRoot X.upperHalf Y e := by
  constructor
  · rintro ⟨x, y, hx, hy, hv⟩
    rcases (split_cover X x).mp hx with hl | hr
    · exact Or.inl ⟨x, y, hl, hy, hv⟩
    · exact Or.inr ⟨x, y, hr, hy, hv⟩
  · rintro (⟨x, y, hx, hy, hv⟩ | ⟨x, y, hx, hy, hv⟩)
    · exact ⟨x, y, lowerHalf_subset hx, hy, hv⟩
    · exact ⟨x, y, upperHalf_subset hx, hy, hv⟩

theorem hasRoot_split_y (X Y : QInterval) (e : Expr) :
    HasRoot X Y e ↔ HasRoot X Y.lowerHalf e ∨ HasRoot X Y.upperHalf e := by
  constructor
  · rintro ⟨x, y, hx, hy, hv⟩
    rcases (split_cover Y y).mp hy with hl | hr
    · exact Or.inl ⟨x, y, hx, hl, hv⟩
    · exact Or.inr ⟨x, y, hx, hr, hv⟩
  · rintro (⟨x, y, hx, hy, hv⟩ | ⟨x, y, hx, hy, hv⟩)
    · exact ⟨x, y, hx, lowerHalf_subset hy, hv⟩
    · exact ⟨x, y, hx, upperHalf_subset hy, hv⟩

def ResultSound (r : BoxResult) (P : Prop) : Prop :=
  (r = .empty → ¬ P) ∧ (r = .present → P)

/-- Presence needs one child; absence needs both; otherwise unknown. -/
def mergeResults : BoxResult → BoxResult → BoxResult
  | .present, _ => .present
  | _, .present => .present
  | .empty, .empty => .empty
  | _, _ => .unknown

theorem mergeResults_sound {a b : BoxResult} {P Q : Prop}
    (ha : ResultSound a P) (hb : ResultSound b Q) :
    ResultSound (mergeResults a b) (P ∨ Q) := by
  cases a <;> cases b <;> simp_all [ResultSound, mergeResults]

theorem resultSound_of_iff {r : BoxResult} {P Q : Prop}
    (h : P ↔ Q) (hs : ResultSound r P) : ResultSound r Q :=
  ⟨fun hr hq => hs.1 hr (h.mpr hq), fun hr => h.mp (hs.2 hr)⟩

theorem classifyBox_sound {B : Backend} (hB : BackendSound B)
    (X Y : QInterval) (e : Expr) : ResultSound (classifyBox B X Y e) (HasRoot X Y e) :=
  ⟨classifyBox_empty hB, classifyBox_present hB⟩

inductive SplitAxis | x | y deriving DecidableEq, Repr

/-- Shared bounded refinement. Fuel counts splitting depth, not evaluator calls
or wall time. Only unknown boxes split; both closed children retain boundaries. -/
def refineBoxes (check : QInterval → QInterval → BoxResult)
    (fuel : Nat) (axis : SplitAxis) (X Y : QInterval) : BoxResult :=
  match fuel with
  | 0 => check X Y
  | n + 1 => match check X Y with
    | .empty => .empty
    | .present => .present
    | .unknown => match axis with
      | .x => mergeResults (refineBoxes check n .y X.lowerHalf Y)
                           (refineBoxes check n .y X.upperHalf Y)
      | .y => mergeResults (refineBoxes check n .x X Y.lowerHalf)
                           (refineBoxes check n .x X Y.upperHalf)

theorem refineBoxes_sound {check : QInterval → QInterval → BoxResult}
    {P : QInterval → QInterval → Prop}
    (hc : ∀ X Y, ResultSound (check X Y) (P X Y))
    (hx : ∀ X Y, P X Y ↔ P X.lowerHalf Y ∨ P X.upperHalf Y)
    (hy : ∀ X Y, P X Y ↔ P X Y.lowerHalf ∨ P X Y.upperHalf)
    (fuel : Nat) (axis : SplitAxis) (X Y : QInterval) :
    ResultSound (refineBoxes check fuel axis X Y) (P X Y) := by
  induction fuel generalizing axis X Y with
  | zero => exact hc X Y
  | succ n ih =>
    have hs := hc X Y
    cases h : check X Y with
    | empty => simpa [refineBoxes,h] using hs
    | present => simpa [refineBoxes,h] using hs
    | unknown =>
      simp only [refineBoxes,h]
      cases axis with
      | x =>
        exact resultSound_of_iff (hx X Y).symm
          (mergeResults_sound (ih .y X.lowerHalf Y) (ih .y X.upperHalf Y))
      | y =>
        exact resultSound_of_iff (hy X Y).symm
          (mergeResults_sound (ih .x X Y.lowerHalf) (ih .x X Y.upperHalf))

/-- The existing ordinary-expression interface specializes the shared recursion. -/
def subdivide (fuel : Nat) (axis : SplitAxis) (B : Backend)
    (X Y : QInterval) (e : Expr) : BoxResult :=
  refineBoxes (fun X Y => classifyBox B X Y e) fuel axis X Y

/-- Compatibility with the original zero-fuel defining equation. -/
theorem subdivide_zero (axis : SplitAxis) (B : Backend) (X Y : QInterval) (e : Expr) :
    subdivide 0 axis B X Y e = classifyBox B X Y e := rfl

/-- Compatibility with the original recursive step, including axis alternation
and unchanged early return/aggregation behavior. -/
theorem subdivide_succ (n : Nat) (axis : SplitAxis) (B : Backend)
    (X Y : QInterval) (e : Expr) :
    subdivide (n+1) axis B X Y e =
      match classifyBox B X Y e with
      | .empty => .empty
      | .present => .present
      | .unknown => match axis with
        | .x => mergeResults (subdivide n .y B X.lowerHalf Y e)
            (subdivide n .y B X.upperHalf Y e)
        | .y => mergeResults (subdivide n .x B X Y.lowerHalf e)
            (subdivide n .x B X Y.upperHalf e) := rfl

theorem subdivide_sound {B : Backend} (hB : BackendSound B)
    (fuel : Nat) (axis : SplitAxis) (X Y : QInterval) (e : Expr) :
    ResultSound (subdivide fuel axis B X Y e) (HasRoot X Y e) :=
  refineBoxes_sound (fun X Y => classifyBox_sound hB X Y e)
    (fun X Y => hasRoot_split_x X Y e) (fun X Y => hasRoot_split_y X Y e) fuel axis X Y

def refineBox (fuel : Nat) (B : Backend) (X Y : QInterval) (e : Expr) : BoxResult :=
  subdivide fuel .x B X Y e

theorem refineBox_empty {B : Backend} (hB : BackendSound B)
    {fuel : Nat} {X Y : QInterval} {e : Expr}
    (h : refineBox fuel B X Y e = .empty) : ¬ HasRoot X Y e :=
  (subdivide_sound hB fuel .x X Y e).1 h

theorem refineBox_present {B : Backend} (hB : BackendSound B)
    {fuel : Nat} {X Y : QInterval} {e : Expr}
    (h : refineBox fuel B X Y e = .present) : HasRoot X Y e :=
  (subdivide_sound hB fuel .x X Y e).2 h

theorem refineBox_zero (B : Backend) (X Y : QInterval) (e : Expr) :
    refineBox 0 B X Y e = classifyBox B X Y e := rfl

end GeneralizedIntervalArithmetic
