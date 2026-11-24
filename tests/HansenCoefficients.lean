import HansenCoefficients
import AuditPolicy
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
namespace GeneralizedIntervalArithmetic.HansenCoefficientsChecks
open HansenCoefficients
open scoped BigOperators

def zero : QInterval := ⟨0,0,by norm_num⟩
def one : QInterval := ⟨1,1,by norm_num⟩
def offset : QInterval := ⟨1,2,by norm_num⟩
def symmetric : QInterval := ⟨-1,1,by norm_num⟩
def coefficients : Fin 2 → QInterval := ![⟨2,4,by norm_num⟩,⟨-3,-1,by norm_num⟩]
def point : Fin 2 → ℝ := ![-2,3]

theorem mixed_bounds : lower offset coefficients point = -16 ∧ upper offset coefficients point = -5 := by
  norm_num [lower,upper,value,lowChoice,highChoice,offset,coefficients,point,Fin.sum_univ_two]

theorem mixed_exact : values offset coefficients point = Set.Icc (-16:ℝ) (-5) := by
  rw [exact_interval,mixed_bounds.1,mixed_bounds.2]

theorem mixed_attained : (-16:ℝ) ∈ values offset coefficients point ∧
    (-5:ℝ) ∈ values offset coefficients point := by
  simpa [mixed_bounds] using attained offset coefficients point

theorem interior_attained : (-10:ℝ) ∈ values offset coefficients point := by
  rw [mixed_exact]; norm_num

theorem all_lower_not_lower : (-16:ℝ) < (1:ℝ)+2*(-2)+(-3)*3 := by norm_num

theorem printed_domain : SignedDomain ![2,3] point := by
  intro i
  fin_cases i <;> norm_num [point]

theorem zero_coordinate : values offset (fun _ : Fin 2 => symmetric) (fun _=>0) =
    Set.Icc (1:ℝ) 2 := by
  rw [exact_interval]
  simp [lower,upper,value,lowChoice,highChoice,offset]

theorem zero_radius : SignedDomain (fun _ : Fin 2 => 0) (fun _=>0) := by
  intro i; simp

theorem zero_dimension : values offset (fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i) =
    Set.Icc (1:ℝ) 2 := by
  rw [exact_interval]
  simp [lower,upper,value,lowChoice,highChoice,offset]

/-- Fixed singleton coefficients show why a two-point parameter restriction
cannot silently become a projected closed interval. -/
theorem singleton_slope (t : Fin 1 → ℝ) : values zero (fun _=>one) t = {t 0} := by
  rw [exact_interval]
  simp [lower,upper,value,lowChoice,highChoice,zero,one]

def signedProjection : Set ℝ := {z | ∃ t : Fin 1 → ℝ,
  SignedDomain (fun _=>1) t ∧ z ∈ values zero (fun _=>one) t}

theorem projected_gap : signedProjection = {(-1:ℝ),1} := by
  ext z
  constructor
  · rintro ⟨t,ht,hz⟩
    rw [singleton_slope,Set.mem_singleton_iff] at hz
    rcases ht 0 with h | h <;> simp [hz,h]
  · intro hz
    rcases hz with hz | hz
    · subst z
      refine ⟨(fun _=>-1),fun _=>Or.inl rfl,?_⟩
      rw [singleton_slope]; rfl
    · have hz' : z=1 := hz
      subst z
      refine ⟨(fun _=>1),fun _=>Or.inr rfl,?_⟩
      rw [singleton_slope]; rfl

theorem zero_not_projected : (0:ℝ) ∉ signedProjection := by rw [projected_gap]; norm_num

/-- Pointwise upper endpoints may require incompatible whole coefficient
witnesses at the two parameter points. -/
theorem maxima_pointwise (t : Fin 1 → ℝ) (ht : SignedDomain (fun _=>1) t) :
    (1:ℝ) ∈ values zero (fun _=>symmetric) t := by
  rw [exact_interval]
  rcases ht 0 with h | h <;>
    norm_num [lower,upper,value,lowChoice,highChoice,zero,symmetric,h]

theorem no_common_maximum : ¬ realizes zero (fun _ : Fin 1 => symmetric)
    {t | SignedDomain (fun _=>1) t} (fun _=>1) := by
  rintro ⟨⟨p,q⟩,hw,hf⟩
  have hp : p=0 := by
    have h := hw.1
    norm_num [zero,QInterval.Contains] at h
    exact le_antisymm h.2 h.1
  have h1 := hf (fun _=>1) (fun _=>Or.inr rfl)
  have hn := hf (fun _=>-1) (fun _=>Or.inl rfl)
  simp [value,hp] at h1 hn
  linarith

end GeneralizedIntervalArithmetic.HansenCoefficientsChecks
#audit_namespace GeneralizedIntervalArithmetic.HansenCoefficientsChecks
