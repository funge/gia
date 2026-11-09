import AffineDomainGuards
import AuditPolicy

namespace GeneralizedIntervalArithmetic.TwoParameterChecks

def lower : RationalAffineForm := ⟨2,-3,1⟩
def upper : RationalAffineForm := ⟨3,-2,1⟩

theorem computed_valid : affineSquareOrdered lower upper = true := by decide +kernel

theorem all_fibers : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    ∃ z, (FunctionalBounds.mk lower.value upper.value).Contains (x,y) z :=
  (affine_square_fibers_iff lower upper).mp computed_valid

/-- Both coordinates remain shared with the actual expression semantics. -/
theorem semantic_lower (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) :
    ∃ z, Value x y lower.expression z ∧
      (FunctionalBounds.mk lower.value upper.value).Contains (x,y) z := by
  exact ⟨lower.value (x,y),affine_form_value lower (x,y),le_refl _,
    (affine_square_ordered_iff lower upper).mp computed_valid x hx y hy⟩

def zero : RationalAffineForm := ⟨0,0,0⟩
def difference : RationalAffineForm := ⟨1,-1,0⟩

/-- Checking the whole diagonal still misses an invalid off-diagonal corner. -/
theorem diagonal_control :
    (∀ t : ℝ, zero.value (t,t) ≤ difference.value (t,t)) ∧
    affineSquareOrdered zero difference = false ∧
    difference.value (0,1) < zero.value (0,1) := by
  constructor
  · intro t; simp [zero,difference,RationalAffineForm.value]
  constructor
  · decide +kernel
  · norm_num [zero,difference,RationalAffineForm.value]

/-- Failure is not absence: this pair has a valid zero fiber on the diagonal. -/
theorem failed_test_retains_fiber :
    (FunctionalBounds.mk zero.value difference.value).Contains (0,0) 0 := by
  norm_num [FunctionalBounds.Contains,zero,difference,RationalAffineForm.value]

def missingLast : RationalAffineForm := ⟨-1,-1,1⟩

theorem three_corners_insufficient :
    0 ≤ missingLast.valueRat (0,0) ∧ 0 ≤ missingLast.valueRat (1,0) ∧
    0 ≤ missingLast.valueRat (0,1) ∧ affineSquareOrdered zero missingLast = false := by
  decide +kernel

/-- The corner criterion cannot be generalized to arbitrary nonlinear bounds. -/
theorem nonlinear_control :
    (∀ x ∈ ({0,1}:Set ℝ), ∀ y ∈ ({0,1}:Set ℝ), 0 ≤ x*(x-1)+0*y) ∧
    (1/2:ℝ)*((1/2)-1) < 0 := by
  constructor
  · intro x hx y _
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> norm_num
  · norm_num

/-- The source parameter domain matters even for affine functions. -/
theorem outside_square_control :
    affineSquareOrdered zero (RationalAffineForm.mk 1 0 0) = true ∧
    (RationalAffineForm.mk 1 0 0).value (-1,0) < 0 := by
  constructor
  · decide +kernel
  · norm_num [RationalAffineForm.value]

end GeneralizedIntervalArithmetic.TwoParameterChecks
#audit_namespace GeneralizedIntervalArithmetic.TwoParameterChecks
