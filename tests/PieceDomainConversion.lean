import PieceDomainConversion
import AuditPolicy
namespace GeneralizedIntervalArithmetic.PieceDomainConversionChecks
open PieceDomainConversion MixedEndpoints FiniteGuardPieces

def one : Band := ⟨1,0,1,0,false,false,[]⟩
def openOne : Band := { one with lowerOpen := true }
def negative : Band := { one with guards := [(⟨0,1⟩,true)] }
def positive : Band := { one with guards := [(⟨0,-1⟩,true)] }
def sloped : Band := ⟨0,1,1,0,false,false,[]⟩
def slopedOpen : Band := { sloped with upperOpen := true }

macro "checkCode" : tactic => `(tactic| norm_num [active?,possible?,definite?,
  PieceDomainConversion.classify,test,compileDomain,compileValues,domainCode,valueCode,
  converted,activeGuard,Description.compile,meet,band,guardAtoms,lower,upper,Atom.test,
  Band.lower,Band.upper,QAffine.ofCoefficients,QAffine.sub,
  one,openOne,negative,positive,sloped,slopedOpen])

theorem singleton_ok : active? one 0 = true := by checkCode
theorem open_singleton_empty : active? openOne 0 = false := by checkCode
theorem equal_sloped_closed : active? sloped 1 = true := by checkCode
theorem equal_sloped_open : active? slopedOpen 1 = false := by checkCode
theorem reversed_sloped : active? sloped 2 = false := by checkCode
theorem interior_sloped : active? slopedOpen (1/2) = true := by checkCode

theorem empty_classification : PieceDomainConversion.classify [] 0 = .falseOnly := by checkCode
theorem all_defined : PieceDomainConversion.classify [one,one] 0 = .trueOnly := by checkCode
theorem mixed_choices : PieceDomainConversion.classify [one,openOne] 0 = .both := by checkCode
theorem pole_absent : PieceDomainConversion.classify [negative,positive] 0 = .falseOnly := by checkCode
theorem negative_side_mixed : PieceDomainConversion.classify [negative,positive] (-1) = .both := by checkCode
theorem positive_side_mixed : PieceDomainConversion.classify [negative,positive] 1 = .both := by checkCode

theorem compiled_domain_at_hole : test (compileDomain [negative,positive]) 0 0 = false := by checkCode
theorem compiled_value_at_hole : test (compileValues [negative,positive]) 0 1 = false := by checkCode
theorem compiled_value_off_hole : test (compileValues [negative,positive]) (1/2) 1 = true := by checkCode

/-- Value-only closure really creates a value, whereas the coupled conversion does not. -/
theorem closure_loses_hole :
    (1:ℝ) ∈ (valueCode positive).denote 0 ∧ (source [negative,positive] 0) = ∅ := by
  constructor
  · rw [valueCode_exact]
    norm_num [positive,one,Band.lowerValue,Band.upperValue]
  · apply Set.eq_empty_iff_forall_not_mem.mpr
    intro z hz
    have hp : possible? [negative,positive] (0:ℚ) = true :=
      (possible_test_exact _ _).2 (by
        obtain ⟨b,hb,hz⟩ := hz
        exact ⟨b,hb,z,by simpa using hz⟩)
    have hf : possible? [negative,positive] 0 = false := by checkCode
    rw [hf] at hp
    contradiction

theorem raw_closed_open_singleton : (1:ℝ) ∈ (valueCode openOne).denote 0 ∧
    ((converted openOne).denote 0) = ∅ := by
  refine ⟨?_,Set.not_nonempty_iff_eq_empty.mp ?_⟩
  · rw [valueCode_exact]; norm_num [openOne,one,Band.lowerValue,Band.upperValue]
  · rw [converted_nonempty]
    intro h
    have hp : active? openOne 0 = true := (active_test_exact _ _).2 (by simpa using h)
    rw [open_singleton_empty] at hp
    contradiction

/-- Numeric closure is an enclosure, not equality of represented output sets. -/
theorem closure_adds_boundary : (1:ℝ) ∈ (converted slopedOpen).denote (1/2) ∧
    (1:ℝ) ∉ slopedOpen.denote (1/2) := by
  constructor
  · apply (converted_exact _ _ _).2
    constructor
    · norm_num [slopedOpen,sloped,Band.lowerValue,Band.upperValue]
    · simpa using (active_test_exact slopedOpen (1/2)).1 interior_sloped
  · simp [slopedOpen,sloped,Band.denote,Band.upperValue]

/-- The aggregate union is nonempty, yet one original choice remains undefined. -/
theorem union_does_not_imply_all : (source [one,openOne] 0).Nonempty ∧
    ¬ (targetDomain [one,openOne]).definite 0 := by
  constructor
  · have h := (possible_test_exact [one,openOne] 0).1 (by checkCode)
    obtain ⟨b,hb,z,hz⟩ := h
    exact ⟨z,b,hb,by simpa using hz⟩
  · rw [← (classification_exact [one,openOne] 0).1]
    intro h
    have hd : definite? [one,openOne] 0 = true :=
      (executable_domain_exact _ _).1.mpr (by simpa using h)
    have hf : definite? [one,openOne] 0 = false := by checkCode
    rw [hf] at hd
    contradiction

/-- Execute the same pure reference functions; the preceding theorems independently
check the results in the kernel. This is not hardware interval evaluation. -/
def executableControls : IO Unit := do
  let actual := [active? one 0, active? openOne 0, active? sloped 2,
    active? slopedOpen (1/2), possible? [negative,positive] 0,
    possible? [negative,positive] 1, definite? [negative,positive] 1,
    definite? [one,one] 0, definite? [] 0]
  unless actual == [true,false,false,true,false,true,false,true,false] do
    throw (IO.userError "finite value/domain reference regression")

#eval executableControls

#audit_namespace GeneralizedIntervalArithmetic.PieceDomainConversionChecks
end GeneralizedIntervalArithmetic.PieceDomainConversionChecks
