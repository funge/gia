import SignedExtraction
import AuditPolicy
namespace GeneralizedIntervalArithmetic.SignedExtractionChecks
open SignedExtraction

/-- The selected half-integer convention is consistent on both signs. -/
theorem half_ties : digit (1/2:ℚ)=0 ∧ digit (-1/2:ℚ)=-1 ∧ digit (-5/2:ℚ)=-3 := by
  norm_num [digit]

theorem half_den : (1/2:ℚ).den=2 := by
  have h := Rat.den_div_eq_of_coprime (a:=1) (b:=2) (by decide) (by decide)
  norm_num only [Int.cast_ofNat] at h
  exact Int.ofNat_inj.mp h

theorem thirds_den : (2/3:ℚ).den=3 := by
  have h := Rat.den_div_eq_of_coprime (a:=2) (b:=3) (by decide) (by decide)
  norm_num only [Int.cast_ofNat] at h
  exact Int.ofNat_inj.mp h

theorem twelfths_den : (5/12:ℚ).den=12 := by
  have h := Rat.den_div_eq_of_coprime (a:=5) (b:=12) (by decide) (by decide)
  norm_num only [Int.cast_ofNat] at h
  exact Int.ofNat_inj.mp h

theorem positive_half : extract (1/2) = some (0,[2]) := by
  norm_num [extract,half_den,thirds_den,twelfths_den,findStop,coeff,orbit,next,residual,digit,segment]

theorem negative_half : extract (-1/2) = some (-1,[2]) := by
  norm_num [extract,half_den,thirds_den,twelfths_den,findStop,coeff,orbit,next,residual,digit,segment]

theorem signed_finite_cases : extract (2/3)=some (1,[-3]) ∧
    extract (-2/3)=some (-1,[3]) ∧ extract (5/12)=some (0,[2,2,2]) ∧
    extract (-5/12)=some (0,[-2,-3,2]) := by
  norm_num [extract,half_den,thirds_den,twelfths_den,findStop,coeff,orbit,next,residual,digit,segment]

/-- -2 is permitted as the head of an integer, not as a finite tail end. -/
theorem integer_cases : extract (-2)=some (-2,[]) ∧ extract 0=some (0,[]) := by
  norm_num [extract,half_den,thirds_den,twelfths_den,findStop,coeff,orbit,next,residual,digit,segment]

theorem fuel_exhaustion : findStop (1/2) 1 = none ∧ findStop (1/2) 2 = some 1 := by
  norm_num [findStop,next,residual,digit]

theorem wrong_tie_control : (⌊(1/2:ℚ)+1/2⌋:ℤ)=1 ∧
    (1/((1/2:ℚ)-1):ℚ)=-2 ∧ ¬RedundantCF.FiniteTail [-2] ∧
    ContinuedFractionConversion.finiteValue 1 [-2]=(1/2:ℚ) := by
  norm_num [RedundantCF.FiniteTail,ContinuedFractionConversion.finiteValue_cons,
    ContinuedFractionConversion.finiteValue_nil]

theorem real_rational_agreement (q : ℚ) (n : ℕ) :
    orbit (q:ℝ) n = (orbit (K:=ℚ) q n:ℝ) ∧ coeff (q:ℝ) n = coeff q n := by
  exact ⟨orbit_cast q n,congrFun (coeff_cast q) n⟩

theorem sqrt_two_infinite : RedundantCF.Admissible (coeff (Real.sqrt 2)) ∧
    RedundantCF.Represents (coeff (Real.sqrt 2)) (Real.sqrt 2) := by
  have hn : NeverStops (Real.sqrt 2) := (never_stops_iff_irrational _).2 (by
    rintro ⟨q,hq⟩
    exact irrational_sqrt_two ⟨q,hq.symm⟩)
  exact ⟨infinite_admissible hn,infinite_recovers hn⟩

theorem all_rationals_extract (q : ℚ) : ∃ a bs,
    extract q=some (a,bs) ∧ RedundantCF.FiniteTail bs ∧
    ContinuedFractionConversion.finiteValue (a:ℚ) (bs.map (fun b : ℤ => (b:ℚ)))=q :=
  rational_extracts q

theorem denominator_control : (next (5/12:ℚ)).den=5 ∧
    (next (next (5/12:ℚ))).den=2 := by
  have h1 : (12/5:ℚ).den=5 := by
    have h := Rat.den_div_eq_of_coprime (a:=12) (b:=5) (by decide) (by decide)
    norm_num only [Int.cast_ofNat] at h
    exact Int.ofNat_inj.mp h
  have h2 : (5/2:ℚ).den=2 := by
    have h := Rat.den_div_eq_of_coprime (a:=5) (b:=2) (by decide) (by decide)
    norm_num only [Int.cast_ofNat] at h
    exact Int.ofNat_inj.mp h
  norm_num [next,residual,digit,h1,h2]

#eval [extract (1/2),extract (-1/2),extract (2/3),extract (-5/12),extract (-2)]
#eval (findStop (5/12) (5/12:ℚ).den, (next (5/12:ℚ)).den)
#audit_namespace GeneralizedIntervalArithmetic.SignedExtractionChecks
end GeneralizedIntervalArithmetic.SignedExtractionChecks
