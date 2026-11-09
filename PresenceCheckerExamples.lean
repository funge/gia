import PresenceChecker
import PresenceExamples

namespace GeneralizedIntervalArithmetic.CheckerExamples

open PresenceExamples

theorem quadratic_certificate :
    certifySegment exactBackend X Y quadratic (1, 0) (2, 0) = true := by decide +kernel

theorem reversed_certificate :
    certifySegment exactBackend X Y quadratic (2, 0) (1, 0) = true := by decide +kernel

theorem rational_classified_present :
    classifyWithSegment exactBackend X Y rationalCurve (1, 0) (2, 0) = .present := by
  decide +kernel

theorem positive_constant_empty :
    classifyWithSegment exactBackend X Y (.const 1) (1, 0) (2, 0) = .empty := by
  decide +kernel

theorem pole_stays_unknown :
    classifyWithSegment exactBackend crossing Y pole (-1, 0) (1, 0) = .unknown := by
  decide +kernel

theorem out_of_box_rejected :
    certifySegment exactBackend X Y .x (-1, 0) (1, 0) = false := by decide +kernel

def boundaryX : QInterval := ⟨0, 1, by norm_num⟩

theorem endpoint_root_present :
    classifyWithSegment exactBackend boundaryX Y .x (0, 0) (1, 0) = .present := by
  decide +kernel

theorem degenerate_root_present :
    classifyWithSegment exactBackend boundaryX Y .x (0, 0) (0, 0) = .present := by
  decide +kernel

theorem no_certified_signs_unknown :
    classifyWithSegment exactBackend crossing Y (.add (.mul .x .x) (.const 1))
      (-1, 0) (1, 0) = .unknown := by decide +kernel

theorem conversion_failure_unknown :
    classifyWithSegment (directedBackend (fun _ => none) some) X Y quadratic
      (1, 0) (2, 0) = .unknown := by decide +kernel

end GeneralizedIntervalArithmetic.CheckerExamples
