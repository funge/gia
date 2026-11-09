import SegmentSearch

namespace GeneralizedIntervalArithmetic.SearchExamples

def box : QInterval := ⟨-1, 1, by norm_num⟩
def circle : Expr := .sub (.add (.mul .x .x) (.mul .y .y)) (.const (1/4))

/-- A small closed curve with positive corner values is found using its negative
center value. The returned pair is a segment certificate, not a root coordinate. -/
theorem circle_certificate :
    searchSegments exactBackend box box circle (boxSegments box box) =
      some ((0, 0), (-1, -1)) := by decide +kernel

theorem circle_present : classifyBox exactBackend box box circle = .present := by
  decide +kernel

theorem circle_has_defined_root :
    ∃ x y, box.Contains x ∧ box.Contains y ∧ Value x y circle 0 :=
  classifyBox_present exactBackend_sound circle_present

theorem invalid_candidate_skipped :
    searchSegments exactBackend box box circle
      [((2, 2), (3, 3)), ((0, 0), (1, 0))] = some ((0, 0), (1, 0)) := by
  decide +kernel

theorem positive_constant_empty : classifyBox exactBackend box box (.const 1) = .empty := by
  decide +kernel

theorem empty_candidates_unknown :
    classifyWithSearch exactBackend box box circle [] = .unknown := by decide +kernel

theorem pole_unknown :
    classifyBox exactBackend box box (.div (.const 1) .x) = .unknown := by decide +kernel

theorem degenerate_box_present :
    classifyBox exactBackend (.point 0) (.point 0) .x = .present := by decide +kernel

theorem shifted_box_present :
    classifyBox exactBackend ⟨1, 2, by norm_num⟩ ⟨2, 4, by norm_num⟩
      (.sub .x (.const (3/2))) = .present := by decide +kernel

theorem conversion_failure_unknown :
    classifyBox (directedBackend (fun _ => none) some) box box circle = .unknown := by
  decide +kernel

def tangentFactor : Expr := .sub .x (.const (1/4))
def tangency : Expr := .mul tangentFactor tangentFactor

/-- No sampled endpoint is the root x=1/4, and no endpoint pair certifies signs.
Unknown remains honest despite a defined root in the box. -/
theorem tangency_unknown : classifyBox exactBackend box box tangency = .unknown := by
  decide +kernel

theorem tangency_has_defined_root :
    ∃ x y, box.Contains x ∧ box.Contains y ∧ Value x y tangency 0 := by
  have hv : Value (1/4 : ℝ) 0 tangentFactor 0 := by
    convert Value.sub (Value.x (x := (1/4 : ℝ)) (y := 0)) (Value.const (1/4)) using 1
    norm_num [tangentFactor]
  refine ⟨1/4, 0, ?_, ?_, ?_⟩
  · norm_num [box, QInterval.Contains]
  · norm_num [box, QInterval.Contains]
  · simpa [tangency] using Value.mul hv hv

end GeneralizedIntervalArithmetic.SearchExamples
