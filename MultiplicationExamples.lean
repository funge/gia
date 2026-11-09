import LinearMultiplication

namespace GeneralizedIntervalArithmetic.MultiplicationExamples

def parameter : QAffine := ⟨0, 1⟩
def complement : QAffine := ⟨1, 0⟩
def zero : LinearInterval := .exact ⟨0, 0⟩
def one : LinearInterval := .exact ⟨1, 1⟩

/-- The product retains sloping bounds; it is not replaced with a constant hull. -/
theorem square_coefficients :
    ((LinearInterval.exact parameter).mul (.exact parameter)).lower = ⟨-1/4, 3/4⟩ ∧
    ((LinearInterval.exact parameter).mul (.exact parameter)).upper = ⟨0, 1⟩ := by
  decide +kernel

theorem square_enclosed {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ((LinearInterval.exact parameter).mul (.exact parameter)).Contains t (t*t) := by
  have hv : (LinearInterval.exact parameter).Contains t t := by
    simp [LinearInterval.Contains, LinearInterval.exact, parameter, QAffine.value]
  exact linear_mul_encloses ht hv hv

theorem complement_product_hull :
    ((LinearInterval.exact parameter).mul (.exact complement)).hull.lo = 0 ∧
    ((LinearInterval.exact parameter).mul (.exact complement)).hull.hi = 1/4 := by
  decide +kernel

theorem ordinary_complement_product_hull :
    ((LinearInterval.exact parameter).hull.mul
      (LinearInterval.exact complement).hull).hi = 1 := by decide +kernel

theorem opposite_slope_bounds :
    (parameter.productBounds complement).lower = ⟨0, 0⟩ ∧
    (parameter.productBounds complement).upper = ⟨1/4, 1/4⟩ := by decide +kernel

theorem constant_product_exact :
    (one.mul (.exact parameter)).lower = parameter ∧
    (one.mul (.exact parameter)).upper = parameter := by decide +kernel

def crossing : LinearInterval := .constant ⟨-1, 2, by norm_num⟩
theorem crossing_product_bounds :
    (crossing.mul crossing).lower = ⟨-2, -2⟩ ∧
    (crossing.mul crossing).upper = ⟨4, 4⟩ := by decide +kernel

/-- Equal uncertain descriptions do not justify treating independent values as a square. -/
theorem crossing_allows_negative_product (t : ℝ) :
    crossing.Contains t (-1) ∧ crossing.Contains t 2 ∧ (-1:ℝ)*2 < 0 := by
  constructor
  · exact (linear_constant_contains _ _ _).mpr (by norm_num [QInterval.Contains])
  constructor
  · exact (linear_constant_contains _ _ _).mpr (by norm_num [QInterval.Contains])
  · norm_num

def everywhere : DomainBounds ℝ := ⟨fun _ => True, fun _ => True, fun _ h => h⟩
def punctured : DomainBounds ℝ := ⟨fun t => t ≠ 0, fun t => t ≠ 0, fun _ h => h⟩
def ZeroValue (t z : ℝ) := t ∈ Set.Icc (0:ℝ) 1 ∧ z = 0
def PuncturedOneValue (t z : ℝ) := t ∈ Set.Icc (0:ℝ) 1 ∧ t ≠ 0 ∧ z = 1

theorem zero_domain_sound : (zero.onDomain everywhere).Sound ZeroValue := by
  refine ⟨?_, fun _ _ h => ⟨h.1, trivial⟩, fun t h => ⟨0, h.1, rfl⟩⟩
  rintro t z ⟨_, rfl⟩
  simp [PartialEnclosure.Sound, LinearInterval.onDomain, FunctionalBounds.Contains,
    zero, LinearInterval.exact, QAffine.value]

theorem punctured_one_sound : (one.onDomain punctured).Sound PuncturedOneValue := by
  refine ⟨?_, fun _ _ h => ⟨h.1, h.2.1⟩, fun t h => ⟨1, h.1, h.2, rfl⟩⟩
  rintro t z ⟨_, _, rfl⟩
  simp [LinearInterval.onDomain, FunctionalBounds.Contains, one,
    LinearInterval.exact, QAffine.value]

theorem partial_zero_product_sound :
    ((zero.mul one).onDomain (everywhere.inter punctured)).Sound
      (ProductValues ZeroValue PuncturedOneValue) :=
  linear_mul_domain_sound zero_domain_sound punctured_one_sound

theorem zero_product_still_undefined :
    ¬ ∃ z, ProductValues ZeroValue PuncturedOneValue 0 z := by
  apply domain_absent partial_zero_product_sound
  intro h
  exact h.2.2 rfl

theorem zero_product_defined_inside :
    ∃ z, ProductValues ZeroValue PuncturedOneValue (1/2) z := by
  apply domain_definite partial_zero_product_sound
  change (1/2:ℝ) ∈ Set.Icc 0 1 ∧ True ∧ (1/2:ℝ) ≠ 0
  norm_num

end GeneralizedIntervalArithmetic.MultiplicationExamples
