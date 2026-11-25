import FractionalProjection
import SplitQuotient
import AuditPolicy
namespace GeneralizedIntervalArithmetic.FractionalProjectionChecks
open FractionalProjection RationalFamilyClosure

def reciprocal : Expr := .div (.const 1) .x
def twiceInverse : Expr := .div (.const 1) reciprocal
def recCoeffs : Coefficients := ⟨0,1,1,0⟩
def idCoeffs : Coefficients := ⟨1,0,0,1⟩
def mobius : Expr := .add (.const 2) (.div (.const (-1)) (.add .x (.const 1)))
def mobCoeffs : Coefficients := ⟨2,1,1,1⟩
def allInputs : List FiniteGuardPieces.Piece := [[]]
def crossing : List FiniteGuardPieces.Piece :=
  (FiniteGuardPieces.band [] ⟨-1,-1⟩ ⟨1,1⟩ false false).compile
def openPositive : List FiniteGuardPieces.Piece :=
  (FiniteGuardPieces.band [] ⟨0,0⟩ ⟨1,1⟩ true false).compile

theorem reciprocal_certificate : Certified recCoeffs reciprocal := by
  norm_num [Certified,Coefficients.Regular,recCoeffs,reciprocal,compile]

theorem twice_inverse_certificate : Certified idCoeffs twiceInverse := by
  norm_num [Certified,Coefficients.Regular,idCoeffs,twiceInverse,reciprocal,compile]

theorem mobius_certificate : Certified mobCoeffs mobius := by
  norm_num [Certified,Coefficients.Regular,mobCoeffs,mobius,compile]
  have hc : MvPolynomial.C (2:ℚ) = (2:Polynomial) := map_ofNat _ 2
  rw [hc]
  ring

theorem all_inputs (t x : ℝ) : x ∈ FiniteGuardPieces.pieces allInputs t := by
  simp [allInputs,FiniteGuardPieces.pieces,IntervalSetDenotation.denote,FiniteGuardPieces.piece]

theorem cancellation_image (t z : ℝ) : z ∈ Image allInputs twiceInverse t ↔ z ≠ 0 := by
  rw [projection_exact twice_inverse_certificate]
  simp [Describes,idCoeffs,inverse,all_inputs,Admitted,compile,twiceInverse,reciprocal,
    evalAt,MvPolynomial.coe_eval₂Hom]

theorem mobius_image (t z : ℝ) : z ∈ Image allInputs mobius t ↔ z ≠ 2 := by
  rw [projection_exact mobius_certificate]
  constructor
  · intro h
    have hn := h.1
    norm_num [mobCoeffs] at hn
    intro he; subst z; norm_num at hn
  · intro hn
    have hn' : (mobCoeffs.a:ℝ)-mobCoeffs.c*z ≠ 0 := by
      simp only [mobCoeffs,Rat.cast_one,Rat.cast_ofNat,one_mul]
      exact sub_ne_zero.mpr (Ne.symm hn)
    refine ⟨hn',all_inputs _ _,?_⟩
    have hd := inverse_denominator_nonzero mobius_certificate.1 hn'
    simpa [Admitted,compile,mobius,evalAt,MvPolynomial.coe_eval₂Hom,mobCoeffs] using hd

theorem crossing_input (t x : ℝ) : x ∈ FiniteGuardPieces.pieces crossing t ↔ -1 ≤ x ∧ x ≤ 1 := by
  rw [crossing,FiniteGuardPieces.band_exact]
  simp [FiniteGuardPieces.guardHolds,QAffine.value]
  intro h; constructor <;> intro hh <;> linarith

theorem reciprocal_rays (t z : ℝ) : z ∈ Image crossing reciprocal t ↔ z ≤ -1 ∨ 1 ≤ z := by
  have he : z ∈ Image crossing reciprocal t ↔ ∃x : ℝ, -1 ≤ x ∧ x ≤ 1 ∧ x ≠ 0 ∧ z=1/x := by
    simp [Image,crossing_input,graph_exact,reciprocal,Admitted,compile,result,evalAt,
      MvPolynomial.coe_eval₂Hom,and_assoc]
  rw [he]
  simpa using SplitQuotient.reciprocal_image (z:=z) (l:= -1) (u:=1) (by norm_num) (by norm_num)

theorem exact_beats_hull : (0:ℝ) ∉ Image crossing reciprocal 0 ∧
    (0:ℝ) ∈ ExtendedImageHull.hull (Image crossing reciprocal 0) := by
  refine ⟨by rw [reciprocal_rays]; norm_num,?_⟩
  have h1 := ExtendedImageHull.sound (Image crossing reciprocal 0)
    ((reciprocal_rays 0 (-1)).2 (by norm_num))
  have h2 := ExtendedImageHull.sound (Image crossing reciprocal 0)
    ((reciprocal_rays 0 1).2 (by norm_num))
  -- Use the established interval shape of the hull, not an image-attainment claim.
  exact ⟨h1.1.trans (EReal.coe_le_coe_iff.mpr (by norm_num)), (EReal.coe_le_coe_iff.mpr (by norm_num : (0:ℝ) ≤ 1)).trans h2.2⟩

theorem finite_queries :
    test recCoeffs crossing reciprocal 0 (-1) = true ∧
    test recCoeffs crossing reciprocal 0 1 = true ∧
    test recCoeffs crossing reciprocal 0 (1/2) = false ∧
    test recCoeffs crossing reciprocal 0 0 = false ∧
    test recCoeffs openPositive reciprocal 0 1 = true ∧
    test recCoeffs openPositive reciprocal 0 2 = true ∧
    test recCoeffs openPositive reciprocal 0 (-1) = false := by
  simp only [test_exact reciprocal_certificate,test_false_iff reciprocal_certificate]
  simp only [projection_exact reciprocal_certificate]
  norm_num [Describes,recCoeffs,inverse,Admitted,compile,reciprocal,evalAt,
    MvPolynomial.coe_eval₂Hom,crossing,openPositive,FiniteGuardPieces.band_exact,
    FiniteGuardPieces.guardHolds,QAffine.value]

theorem inherited_hole_queries :
    test idCoeffs allInputs twiceInverse 0 0 = false ∧
    test idCoeffs allInputs twiceInverse 0 2 = true ∧
    test mobCoeffs allInputs mobius 0 2 = false ∧
    test mobCoeffs allInputs mobius 0 3 = true := by
  rw [test_false_iff twice_inverse_certificate,test_exact twice_inverse_certificate,
    test_false_iff mobius_certificate,test_exact mobius_certificate]
  norm_num [cancellation_image,mobius_image]

theorem empty_queries : test recCoeffs [] reciprocal 0 1 = false := by
  apply (test_false_iff reciprocal_certificate _ _ _).2
  simp [Image,FiniteGuardPieces.pieces,IntervalSetDenotation.denote]

/-- Without regularity the inverse-based checker is not a complete membership
procedure: a constant value has many preimages, not a unique reconstructed one. -/
def degenerate : Coefficients := ⟨0,1,0,1⟩
theorem regularity_needed : ¬degenerate.Regular ∧
    test degenerate allInputs (.const 1) 0 1 = false ∧
    (1:ℝ) ∈ Image allInputs (.const 1) 0 := by
  refine ⟨by norm_num [degenerate,Coefficients.Regular],by norm_num [test,degenerate],?_⟩
  exact ⟨0,all_inputs _ _,by simpa using (Value.const (x:=0) (y:=0) 1)⟩

def cancelled : Expr := .div (.sub (.mul .x .x) (.const 1)) (.sub .x (.const 1))
def cancelledCoeffs : Coefficients := ⟨1,1,0,1⟩
def parameterHole : Expr := .add cancelled (.mul (.const 0) (.div (.const 1) .y))

theorem cancelled_certificate : Certified cancelledCoeffs cancelled := by
  norm_num [Certified,Coefficients.Regular,cancelledCoeffs,cancelled,compile]
  ring

theorem parameter_hole_certificate : Certified cancelledCoeffs parameterHole := by
  norm_num [Certified,Coefficients.Regular,cancelledCoeffs,parameterHole,cancelled,compile]
  ring

theorem cancelled_image (t z : ℝ) : z ∈ Image allInputs cancelled t ↔ z ≠ 2 := by
  rw [projection_exact cancelled_certificate]
  simp [Describes,cancelledCoeffs,inverse,all_inputs,Admitted,compile,cancelled,
    evalAt,MvPolynomial.coe_eval₂Hom]
  constructor <;> intro h hh <;> apply h <;> linarith

theorem parameter_hole_image (t z : ℝ) :
    z ∈ Image allInputs parameterHole t ↔ z ≠ 2 ∧ t ≠ 0 := by
  rw [projection_exact parameter_hole_certificate]
  simp [Describes,cancelledCoeffs,inverse,all_inputs,Admitted,compile,parameterHole,cancelled,
    evalAt,MvPolynomial.coe_eval₂Hom,forall_and]
  intro _
  constructor <;> intro h hh <;> apply h <;> linarith

theorem canceled_and_parameter_queries :
    test cancelledCoeffs allInputs cancelled 0 2 = false ∧
    test cancelledCoeffs allInputs cancelled 0 3 = true ∧
    test cancelledCoeffs allInputs parameterHole 0 3 = false ∧
    test cancelledCoeffs allInputs parameterHole 1 3 = true := by
  rw [test_false_iff cancelled_certificate,test_exact cancelled_certificate,
    test_false_iff parameter_hole_certificate,test_exact parameter_hole_certificate]
  norm_num [cancelled_image,parameter_hole_image]

#eval [test cancelledCoeffs allInputs cancelled 0 2,
  test cancelledCoeffs allInputs cancelled 0 3,
  test cancelledCoeffs allInputs parameterHole 0 3,
  test cancelledCoeffs allInputs parameterHole 1 3]
#eval [test recCoeffs crossing reciprocal 0 (-1),
  test recCoeffs crossing reciprocal 0 (1/2),
  test idCoeffs allInputs twiceInverse 0 0,
  test mobCoeffs allInputs mobius 0 3]
end GeneralizedIntervalArithmetic.FractionalProjectionChecks
#audit_namespace GeneralizedIntervalArithmetic.FractionalProjectionChecks
