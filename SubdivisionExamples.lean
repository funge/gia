import Subdivision
import SegmentSearchExamples

namespace GeneralizedIntervalArithmetic.SubdivisionExamples
open SearchExamples

def positiveSquare : Expr := .add (.mul .x .x) (.const 1)

theorem positiveSquare_initial_unknown :
    classifyBox exactBackend box box positiveSquare = .unknown := by decide +kernel

theorem positiveSquare_refined_empty :
    refineBox 1 exactBackend box box positiveSquare = .empty := by decide +kernel

theorem positiveSquare_no_root : ¬ HasRoot box box positiveSquare :=
  refineBox_empty exactBackend_sound positiveSquare_refined_empty

theorem tangency_shallow_unknown :
    refineBox 1 exactBackend box box tangency = .unknown := by decide +kernel

theorem tangency_refined_present :
    refineBox 3 exactBackend box box tangency = .present := by decide +kernel

theorem tangency_refined_root : HasRoot box box tangency :=
  refineBox_present exactBackend_sound tangency_refined_present

theorem pole_refined_unknown :
    refineBox 3 exactBackend box box (.div (.const 1) .x) = .unknown := by decide +kernel

theorem degenerate_pole_unknown :
    refineBox 3 exactBackend (.point 0) (.point 0) (.div (.const 1) .x) = .unknown := by
  decide +kernel

theorem failed_conversion_unknown :
    refineBox 2 (directedBackend (fun _ => none) some) box box positiveSquare = .unknown := by
  decide +kernel

theorem empty_unknown_stays_unknown : mergeResults .empty .unknown = .unknown := rfl

theorem unknown_present_is_present : mergeResults .unknown .present = .present := rfl

end GeneralizedIntervalArithmetic.SubdivisionExamples
