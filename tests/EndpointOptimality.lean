import EndpointOptimality
import AuditPolicy
namespace GeneralizedIntervalArithmetic.EndpointOptimalityChecks
open EndpointOptimality DiscreteDemotion
set_option exponentiation.threshold 2048

def zeroWords : HardwareAddition.Bounds Binary64.Word := ⟨0,0⟩
def unitWords : HardwareAddition.Bounds Binary64.Word := ⟨0,0x3ff0000000000000⟩
def wideWords : HardwareAddition.Bounds Binary64.Word := ⟨0xbff0000000000000,0x3ff0000000000000⟩
macro "decode_raw" : tactic => `(tactic| norm_num [Binary64.decode,Binary64.exponent,Binary64.fraction,Binary64.sign,zeroWords,unitWords,wideWords])

theorem decode_zero : Binary64.decode 0 = some 0 := by decode_raw
theorem decode_one : Binary64.decode 0x3ff0000000000000 = some 1 := by decode_raw
theorem decode_negative_one : Binary64.decode 0xbff0000000000000 = some (-1) := by decode_raw

theorem zero_lower : LowerOptimal 0 0 := by
  simpa using (decoded_down_iff decode_zero 0).mp (by simpa using (decoded_fixed decode_zero).1)

theorem one_upper : UpperOptimal 1 1 := by
  simpa using (decoded_up_iff decode_one 1).mp (by simpa using (decoded_fixed decode_one).2)

theorem zero_upper : UpperOptimal 0 0 := by
  simpa using (decoded_up_iff decode_zero 0).mp (by simpa using (decoded_fixed decode_zero).2)

def idealZero : LinearInterval := ⟨⟨0,0⟩,⟨0,0⟩,by norm_num,by norm_num⟩
def wideForm : HardwareAffine.Form Binary64.Word := ⟨wideWords,wideWords⟩

theorem accepts_loose : FiniteAffineDemotion.certify idealZero wideForm = some wideForm := by
  norm_num [FiniteAffineDemotion.certify,idealZero,wideForm,wideWords,
    Binary64.decode,Binary64.exponent,Binary64.fraction,Binary64.sign]

theorem loose_not_optimal : ¬ LowerOptimal 0 (-1) := by
  rintro ⟨_,h⟩
  have hrep := Binary64Format.decoded_repaired decode_zero
  have := h 0 hrep (by norm_num)
  norm_num at this

theorem accepted_not_least : hull binaryValues (Set.Icc (0:ℝ) 0) ≠
    {x | HardwareAddition.Contains Binary64.real wideWords x} := by
  intro h
  have hh := (interval_exact_iff (a:=0) (b:=0) (by norm_num)
    (O:=wideWords) decode_negative_one decode_one (by norm_num) (by norm_num)).mp h
  exact loose_not_optimal hh.1

theorem zero_exact : hull binaryValues (Set.Icc (0:ℝ) 0) =
    {x | HardwareAddition.Contains Binary64.real zeroWords x} :=
  (interval_exact_iff (by norm_num) (O:=zeroWords) decode_zero decode_zero
    (by norm_num) (by norm_num)).mpr ⟨zero_lower,zero_upper⟩

/-- Least closed enclosure does not assert that its endpoints occur in the image. -/
theorem open_image_exact : hull binaryValues (Set.Ioo (0:ℝ) 1) =
    {x | HardwareAddition.Contains Binary64.real unitWords x} := by
  apply (certificate_exact_iff (Set.nonempty_Ioo.mpr (by norm_num))
    (O:=unitWords) decode_zero decode_one ?_).mpr
  · simpa [csInf_Ioo (show (0:ℝ)<1 by norm_num),csSup_Ioo (show (0:ℝ)<1 by norm_num)] using
      And.intro zero_lower one_upper
  · intro x hx
    exact (contains_iff (O:=unitWords) decode_zero decode_one x).mpr (by simpa using And.intro (le_of_lt hx.1) (le_of_lt hx.2))

theorem nonattainment : (0:ℝ) ∈ hull binaryValues (Set.Ioo 0 1) ∧ (0:ℝ) ∉ Set.Ioo 0 1 := by
  rw [open_image_exact]
  exact ⟨(contains_iff (O:=unitWords) decode_zero decode_one 0).mpr (by norm_num),by norm_num⟩

def fiber (b : Bool) : Set ℝ := if b then Set.Ioo 0 1 else ∅

theorem partial_family : ∀ b z, z ∈ hull binaryValues (fiber b) ↔
    (fiber b).Nonempty ∧ HardwareAddition.Contains Binary64.real unitWords z := by
  have h := family_exact Set.univ fiber (fun _ => unitWords) ?_
  · simpa using h
  · intro b _ hn
    cases b
    · simp [fiber] at hn
    · refine ⟨0,1,decode_zero,decode_one,?_,?_⟩
      · intro z hz
        simp only [fiber,if_true] at hz
        exact (contains_iff (O:=unitWords) decode_zero decode_one z).mpr (by simpa using And.intro (le_of_lt hz.1) (le_of_lt hz.2))
      · simpa [fiber,csInf_Ioo (show (0:ℝ)<1 by norm_num),csSup_Ioo (show (0:ℝ)<1 by norm_num)] using
          And.intro zero_lower one_upper

theorem empty_fiber : hull binaryValues (fiber false) = ∅ := by simp [fiber,empty]

end GeneralizedIntervalArithmetic.EndpointOptimalityChecks
#audit_namespace GeneralizedIntervalArithmetic.EndpointOptimalityChecks
