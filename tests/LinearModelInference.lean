import LinearModelInference
import AuditPolicy
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace GeneralizedIntervalArithmetic.LinearModelInferenceChecks
open LinearModelInference

def weights : Fin 2 → ℚ := ![2,-1]
def features : Fin 2 → QInterval := ![⟨1,2,by norm_num⟩,⟨0,1,by norm_num⟩]

theorem exact_bounds : (bounds weights (1/2) features).lo = 3/2 ∧
    (bounds weights (1/2) features).hi = 9/2 := by
  simp only [bounds,IntervalDotProduct.weightedBounds,IntervalDotProduct.bounds,
    QInterval.add,QInterval.point,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  norm_num [weights,features,QInterval.mul]

theorem certified_prediction {x : Fin 2 → ℝ} (hx : IntervalDotProduct.InBox features x) :
    1 < predict (fun i => (weights i : ℝ)) ((1/2:ℚ):ℝ) x := by
  apply above_threshold weights (1/2) (I:=features) _ hx
  rw [exact_bounds.1]
  norm_num

/-- At threshold 2 the outcome really varies over this independent box. -/
theorem threshold_varies :
    (∃ x, IntervalDotProduct.InBox features x ∧ predict (fun i => (weights i : ℝ)) ((1/2:ℚ):ℝ) x < 2) ∧
    (∃ x, IntervalDotProduct.InBox features x ∧ 2 < predict (fun i => (weights i : ℝ)) ((1/2:ℚ):ℝ) x) := by
  obtain ⟨⟨x,hx,hl⟩,⟨y,hy,hu⟩⟩ := extrema weights (1/2) features
  constructor
  · refine ⟨x,hx,?_⟩
    rw [hl,exact_bounds.1]; norm_num
  · refine ⟨y,hy,?_⟩
    rw [hu,exact_bounds.2]; norm_num

/-- Touching the lower endpoint cannot certify a strict threshold. -/
theorem strict_boundary : ¬∀ x, IntervalDotProduct.InBox features x →
    (3/2:ℝ) < predict (fun i => (weights i : ℝ)) ((1/2:ℚ):ℝ) x := by
  intro h
  obtain ⟨x,hx,hl⟩ := (extrema weights (1/2) features).1
  have bad := h x hx
  rw [hl,exact_bounds.1] at bad
  norm_num at bad

theorem no_features (w : Fin 0 → ℚ) (I : Fin 0 → QInterval) (b : ℚ) :
    (bounds w b I).lo = b ∧ (bounds w b I).hi = b := by
  simp [bounds,IntervalDotProduct.weightedBounds,IntervalDotProduct.bounds,QInterval.add,QInterval.point]

open HardwareAddition

def decode (q : ℚ) : Option ℝ := some (q:ℝ)
def addCall (a b : ℚ) : Option (ℚ × ℚ) := some (a+b,a+b)
def mulCall (a b : ℚ) : Option (ℚ × ℚ) := some (a*b,a*b)
def add (A B : Bounds ℚ) : Option (Bounds ℚ) := assemble (addCall A.lo B.lo) (addCall A.hi B.hi)
def mul (A B : Bounds ℚ) : Option (Bounds ℚ) := HardwareMultiplication.assembleFour min max
  (mulCall A.lo B.lo) (mulCall A.lo B.hi) (mulCall A.hi B.lo) (mulCall A.hi B.hi)

theorem add_sound : HardwareIntervalOps.OpSound decode add (· + ·) := by
  apply HardwareSine.add_op_sound
  intro a b; simp [HardwareAddition.CallSound,decode,addCall]

theorem mul_sound : HardwareIntervalOps.OpSound decode mul (· * ·) := by
  apply HardwareSine.mul_op_sound
  · simp [HardwareMultiplication.SelectSound,decode]
  · simp [HardwareMultiplication.SelectSound,decode]
  · intro a b; simp [HardwareMultiplication.CallSound,decode,mulCall]

def W : Fin 2 → Bounds ℚ := ![⟨2,2⟩,⟨-1,-1⟩]
def X : Fin 2 → Bounds ℚ := ![⟨1,2⟩,⟨0,1⟩]
def B : Bounds ℚ := ⟨1/2,1/2⟩

theorem program_result : run add mul 0 W X B = some ⟨3/2,9/2⟩ := by
  norm_num [run,DirectedDotProduct.run,DirectedDotProduct.loop,add,mul,addCall,mulCall,
    assemble,HardwareMultiplication.assembleFour,W,X,B]

theorem program_encloses {x : Fin 2 → ℝ} (hx : IntervalDotProduct.InBox features x) :
    Contains decode (⟨3/2,9/2⟩ : Bounds ℚ) (predict (fun i => (weights i : ℝ)) ((1/2:ℚ):ℝ) x) := by
  apply run_encloses add_sound mul_sound (show decode 0 = some 0 by simp [decode]) _ _ _ program_result
  · intro i; fin_cases i <;> norm_num [W,weights,Contains,decode]
  · intro i
    have h := hx i
    fin_cases i <;> norm_num [features,QInterval.Contains] at h <;>
      simpa [X,Contains,decode] using h
  · norm_num [B,Contains,decode]

def failBias (A B : Bounds ℚ) : Option (Bounds ℚ) :=
  if B.lo = 1/2 then none else add A B

theorem unavailable_bias : run failBias mul 0 W X B = none := by
  norm_num [run,DirectedDotProduct.run,DirectedDotProduct.loop,failBias,add,mul,addCall,mulCall,
    assemble,HardwareMultiplication.assembleFour,W,X,B]

theorem empty_still_adds_bias (I J : Fin 0 → Bounds ℚ) :
    run (fun _ _ => none) mul 0 I J B = none := rfl

#eval run add mul 0 W X B
#eval run failBias mul 0 W X B

end GeneralizedIntervalArithmetic.LinearModelInferenceChecks
#audit_namespace GeneralizedIntervalArithmetic.LinearModelInferenceChecks
