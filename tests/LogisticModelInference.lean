import LogisticModelInference
import AuditPolicy

namespace GeneralizedIntervalArithmetic.LogisticModelInferenceChecks
open LogisticModelInference

def weights : Fin 1 → ℚ := fun _ => 1
def positiveBox : Fin 1 → QInterval := fun _ => ⟨1,2,by norm_num⟩
def mixedBox : Fin 1 → QInterval := fun _ => ⟨-1,1,by norm_num⟩
def touchingBox : Fin 1 → QInterval := fun _ => ⟨0,1,by norm_num⟩

theorem positive_logit_bounds :
    (LinearModelInference.bounds weights 0 positiveBox).lo = 1 ∧
    (LinearModelInference.bounds weights 0 positiveBox).hi = 2 := by
  norm_num [LinearModelInference.bounds,IntervalDotProduct.weightedBounds,
    IntervalDotProduct.bounds,QInterval.add,QInterval.point,QInterval.mul,
    Fin.sum_univ_succ,weights,positiveBox]

theorem certified {x : Fin 1 → ℝ} (hx : IntervalDotProduct.InBox positiveBox x) :
    (1/2:ℝ) < predict (fun i => (weights i : ℝ)) 0 x := by
  apply (half_lt_iff _).2
  have h := (LinearModelInference.sound weights 0 hx).1
  rw [positive_logit_bounds.1] at h
  norm_num at h
  exact lt_of_lt_of_le zero_lt_one h

theorem mixed_witnesses :
    (∃ x, IntervalDotProduct.InBox mixedBox x ∧ predict (fun i => (weights i : ℝ)) 0 x < 1/2) ∧
    (∃ x, IntervalDotProduct.InBox mixedBox x ∧ 1/2 < predict (fun i => (weights i : ℝ)) 0 x) := by
  constructor
  · refine ⟨fun _ => -1, ?_, ?_⟩
    · intro i; norm_num [mixedBox,QInterval.Contains]
    · apply (lt_half_iff _).2
      norm_num [LinearModelInference.predict,IntervalDotProduct.dot,weights,Fin.sum_univ_succ]
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · intro i; norm_num [mixedBox,QInterval.Contains]
    · apply (half_lt_iff _).2
      norm_num [LinearModelInference.predict,IntervalDotProduct.dot,weights,Fin.sum_univ_succ]

theorem boundary_value : predict (fun i => (weights i : ℝ)) 0 (fun _ => 0) = 1/2 := by
  simp [predict,LinearModelInference.predict,IntervalDotProduct.dot,sigmoid_zero]

theorem touching_nonstrict {x : Fin 1 → ℝ} (hx : IntervalDotProduct.InBox touchingBox x) :
    (1/2:ℝ) ≤ predict (fun i => (weights i : ℝ)) 0 x := by
  apply (half_le_iff _).2
  have h := (hx 0).1
  simpa [LinearModelInference.predict,IntervalDotProduct.dot,weights,Fin.sum_univ_succ,
    touchingBox,QInterval.Contains] using h

theorem positive_certificate : LogisticModelInference.classify ⟨1,2,by norm_num⟩ = some true := by decide
theorem negative_certificate : LogisticModelInference.classify ⟨-2,-1,by norm_num⟩ = some false := by decide
theorem mixed_unknown : LogisticModelInference.classify ⟨-1,1,by norm_num⟩ = none := by decide
theorem touching_unknown : LogisticModelInference.classify ⟨0,1,by norm_num⟩ = none := by decide
theorem zero_unknown : LogisticModelInference.classify (QInterval.point 0) = none := by decide

/-- A loose bound can be inconclusive even when the actual logit is positive. -/
theorem unknown_is_not_variation :
    (⟨-1,1,by norm_num⟩ : QInterval).Contains (1/2:ℝ) ∧
    (1/2:ℝ) < sigmoid (1/2) := by
  constructor
  · norm_num [QInterval.Contains]
  · exact (half_lt_iff _).2 (by norm_num)

/- Directed logit API with exact rational mock operations. -/
open HardwareAddition

def decode (q : ℚ) : Option ℝ := some (q:ℝ)
def addCall (a b : ℚ) : Option (ℚ × ℚ) := some (a+b,a+b)
def mulCall (a b : ℚ) : Option (ℚ × ℚ) := some (a*b,a*b)
def add (A B : Bounds ℚ) : Option (Bounds ℚ) := assemble (addCall A.lo B.lo) (addCall A.hi B.hi)
def mul (A B : Bounds ℚ) : Option (Bounds ℚ) :=
  HardwareMultiplication.assembleFour min max
    (mulCall A.lo B.lo) (mulCall A.lo B.hi)
    (mulCall A.hi B.lo) (mulCall A.hi B.hi)

theorem add_sound : HardwareIntervalOps.OpSound decode add (· + ·) := by
  apply HardwareSine.add_op_sound
  intro a b; simp [CallSound,decode,addCall]
theorem mul_sound : HardwareIntervalOps.OpSound decode mul (· * ·) := by
  apply HardwareSine.mul_op_sound
  · simp [HardwareMultiplication.SelectSound,decode]
  · simp [HardwareMultiplication.SelectSound,decode]
  · intro a b; simp [HardwareMultiplication.CallSound,decode,mulCall]

def W : Fin 1 → Bounds ℚ := fun _ => ⟨1,1⟩
def X : Fin 1 → Bounds ℚ := fun _ => ⟨1,2⟩
def B : Bounds ℚ := ⟨0,0⟩

theorem program_result : LinearModelInference.run add mul 0 W X B = some ⟨1,2⟩ := by
  norm_num [LinearModelInference.run,DirectedDotProduct.run,DirectedDotProduct.loop,
    add,mul,addCall,mulCall,assemble,HardwareMultiplication.assembleFour,W,X,B]

theorem program_sigmoid_bounds {x : Fin 1 → ℝ} (hx : IntervalDotProduct.InBox positiveBox x) :
    sigmoid 1 ≤ predict (fun _ => 1) 0 x ∧ predict (fun _ => 1) 0 x ≤ sigmoid 2 := by
  have h := run_encloses add_sound mul_sound (show decode 0 = some 0 by simp [decode])
    (W:=W) (X:=X) (B:=B) (O:=⟨1,2⟩) (w:=fun _ => 1) (x:=x) (b:=0) ?hw ?hx ?hb program_result rfl rfl
  · simpa only [Rat.cast_one, Rat.cast_ofNat] using h
  case hw => intro i; norm_num [W,Contains,decode]
  case hx => intro i; simpa [X,Contains,decode,positiveBox,QInterval.Contains] using hx i
  case hb => norm_num [B,Contains,decode]

theorem program_certifies {x : Fin 1 → ℝ} (hx : IntervalDotProduct.InBox positiveBox x) :
    (1/2:ℝ) < predict (fun _ => 1) 0 x :=
  ((half_lt_iff 1).2 zero_lt_one).trans_le (program_sigmoid_bounds hx).1

/-- Equality is attained: a nonstrict certificate is not a strict one. -/
theorem boundary_not_strict :
    ¬ (1/2:ℝ) < predict (fun i => (weights i : ℝ)) 0 (fun _ => 0) := by
  rw [boundary_value]
  exact lt_irrefl _

#eval LogisticModelInference.classify ⟨1,2,by norm_num⟩
#eval LogisticModelInference.classify ⟨0,1,by norm_num⟩
#eval LinearModelInference.run add mul 0 W X B
end GeneralizedIntervalArithmetic.LogisticModelInferenceChecks
#audit_namespace GeneralizedIntervalArithmetic.LogisticModelInferenceChecks
