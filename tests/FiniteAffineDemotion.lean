import FiniteAffineDemotion
import HardwareSine
import AuditPolicy

namespace GeneralizedIntervalArithmetic.FiniteAffineDemotionChecks
open FiniteAffineDemotion HardwareAddition HardwareAffine HardwareIntervalOps
set_option exponentiation.threshold 2048

-- A genuine uncertain ideal: [t, 1+t], not just an exact central line.
def ideal : LinearInterval := ⟨⟨0,1⟩,⟨1,2⟩,by norm_num,by norm_num⟩
def exactWords : Form Binary64.Word := ⟨⟨0,0x3ff0000000000000⟩,⟨0x3ff0000000000000,0x4000000000000000⟩⟩
def outerWords : Form Binary64.Word := ⟨⟨0xbff0000000000000,0x4000000000000000⟩,⟨0,0x4008000000000000⟩⟩

macro "check_words" : tactic => `(tactic| norm_num [certify,ideal,exactWords,outerWords,
  Binary64.decode,Binary64.exponent,Binary64.fraction,Binary64.sign])

theorem accept_exact : certify ideal exactWords = some exactWords := by check_words
theorem accept_strict_outward : certify ideal outerWords = some outerWords := by check_words

theorem reject_inward_lower : certify ideal
    {exactWords with atZero := ⟨0x3fe0000000000000,0x3ff0000000000000⟩} = none := by check_words
theorem reject_inward_upper : certify ideal
    {exactWords with atOne := ⟨0x3ff0000000000000,0x3ff8000000000000⟩} = none := by check_words

theorem reject_infinity : certify ideal
    {exactWords with atOne := ⟨0x3ff0000000000000,0x7ff0000000000000⟩} = none := by check_words
theorem reject_nan : certify ideal
    {exactWords with atZero := ⟨0,0x7ff8000000000000⟩} = none := by check_words
theorem reject_oversized : certify ideal
    {exactWords with atOne := ⟨2^64,0x4000000000000000⟩} = none := by check_words

theorem accept_negative_zero : certify ideal
    {exactWords with atZero := ⟨0x8000000000000000,0x3ff0000000000000⟩} =
    some {exactWords with atZero := ⟨0x8000000000000000,0x3ff0000000000000⟩} := by check_words

theorem all_ideal_values {t z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hz : t ≤ z ∧ z ≤ 1+t) : HardwareAffine.Contains Binary64.real outerWords t z := by
  apply certified_enclosure accept_strict_outward ht
  simp only [LinearInterval.Contains,ideal,QAffine.value]
  constructor <;> norm_num <;> nlinarith [hz.1,hz.2]

theorem endpoints_and_interior :
    HardwareAffine.Contains Binary64.real outerWords 0 0 ∧
    HardwareAffine.Contains Binary64.real outerWords 1 2 ∧
    HardwareAffine.Contains Binary64.real outerWords (1/2) (5/4) := by
  exact ⟨all_ideal_values (by norm_num) (by norm_num),
    all_ideal_values (by norm_num) (by norm_num),all_ideal_values (by norm_num) (by norm_num)⟩

theorem noncollapse_everywhere (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃ z, HardwareAffine.Contains Binary64.real exactWords t z :=
  certified_noncollapse accept_exact ht

-- Executable reference operations for testing control flow, not a native backend.
def qsub (A B : Bounds ℚ) : Option (Bounds ℚ) := some ⟨A.lo-B.hi,A.hi-B.lo⟩
def qadd (A B : Bounds ℚ) : Option (Bounds ℚ) := some ⟨A.lo+B.lo,A.hi+B.hi⟩
def qmul (A B : Bounds ℚ) : Option (Bounds ℚ) := some
  ⟨min (min (A.lo*B.lo) (A.lo*B.hi)) (min (A.hi*B.lo) (A.hi*B.hi)),
   max (max (A.lo*B.lo) (A.lo*B.hi)) (max (A.hi*B.lo) (A.hi*B.hi))⟩
def qform : Form ℚ := ⟨⟨0,1⟩,⟨1,2⟩⟩

theorem reference_parameters :
    evaluate qsub qmul qadd ⟨1,1⟩ ⟨0,0⟩ qform = some ⟨0,1⟩ ∧
    evaluate qsub qmul qadd ⟨1,1⟩ ⟨1,1⟩ qform = some ⟨1,2⟩ ∧
    evaluate qsub qmul qadd ⟨1,1⟩ ⟨1/2,1/2⟩ qform = some ⟨1/2,3/2⟩ := by norm_num [evaluate,qsub,qmul,qadd,qform]

theorem unavailable_weight : evaluate (fun _ _ => none) qmul qadd ⟨1,1⟩ ⟨0,0⟩ qform = none := by norm_num [evaluate,qsub,qmul,qadd,qform]
theorem unavailable_first_product : evaluate qsub (fun _ _ => none) qadd ⟨1,1⟩ ⟨0,0⟩ qform = none := by norm_num [evaluate,qsub,qmul,qadd,qform]

def failAtOne (A B : Bounds ℚ) : Option (Bounds ℚ) :=
  if B.lo = 1 then none else qmul A B

theorem unavailable_second_product :
    evaluate qsub failAtOne qadd ⟨1,1⟩ ⟨1/2,1/2⟩ qform = none := by norm_num [evaluate,qsub,qmul,qadd,qform,failAtOne]
theorem unavailable_sum : evaluate qsub qmul (fun _ _ => none) ⟨1,1⟩ ⟨0,0⟩ qform = none := by norm_num [evaluate,qsub,qmul,qadd,qform,failAtOne]

-- Discharge OpSound through the existing directed-pair assembly theorems.
-- This connects the proof to the approved contracts without claiming native execution.
theorem directed_evaluation {F : Type} {decode : F → Option ℝ}
    {cs cm ca : F → F → Option (F × F)} {mn mx : F → F → F}
    (hs : ∀ a b, HardwareSubtraction.CallSound decode a b (cs a b))
    (hm : ∀ a b, HardwareMultiplication.CallSound decode a b (cm a b))
    (ha : ∀ a b, HardwareAddition.CallSound decode a b (ca a b))
    (hmin : HardwareMultiplication.SelectSound decode mn min)
    (hmax : HardwareMultiplication.SelectSound decode mx max)
    {one parameter O : Bounds F} {H : Form F} {t z : ℝ}
    (h1 : HardwareAddition.Contains decode one 1)
    (ht : HardwareAddition.Contains decode parameter t)
    (hz : HardwareAffine.Contains decode H t z)
    (he : evaluate
      (fun A B => assemble (cs A.lo B.hi) (cs A.hi B.lo))
      (fun A B => HardwareMultiplication.assembleFour mn mx
        (cm A.lo B.lo) (cm A.lo B.hi) (cm A.hi B.lo) (cm A.hi B.hi))
      (fun A B => assemble (ca A.lo B.lo) (ca A.hi B.hi)) one parameter H = some O) :
    HardwareAddition.Contains decode O z :=
  evaluate_sound (HardwareSine.sub_op_sound hs) (HardwareSine.mul_op_sound hmin hmax hm)
    (HardwareSine.add_op_sound ha) h1 ht hz he

#audit_namespace GeneralizedIntervalArithmetic.FiniteAffineDemotionChecks
end GeneralizedIntervalArithmetic.FiniteAffineDemotionChecks
