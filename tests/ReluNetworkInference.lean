import ReluNetworkInference
import AuditPolicy
import Mathlib.Data.Fin.VecNotation

namespace GeneralizedIntervalArithmetic.ReluNetworkInferenceChecks
open ReluNetworkInference

def W : Fin 2 → Fin 1 → ℚ := fun _ _ => 1
def b : Fin 2 → ℚ := fun _ => 0
def v : Fin 2 → ℚ := ![1,-1]
def I : Fin 1 → QInterval := fun _ => ⟨-1,1,by norm_num⟩

theorem hidden_bounds (j : Fin 2) :
    (hiddenBounds W b I j).lo = 0 ∧ (hiddenBounds W b I j).hi = 1 := by
  norm_num [hiddenBounds,reluBounds,LinearModelInference.bounds,
    IntervalDotProduct.weightedBounds,IntervalDotProduct.bounds,QInterval.add,
    QInterval.point,QInterval.mul,Fin.sum_univ_succ,W,b,I]

theorem output_bounds : (bounds W b v 0 I).lo = -1 ∧ (bounds W b v 0 I).hi = 1 := by
  norm_num [bounds,LinearModelInference.bounds,IntervalDotProduct.weightedBounds,
    IntervalDotProduct.bounds,QInterval.add,QInterval.point,QInterval.mul,
    Fin.sum_univ_succ,v,hidden_bounds]

/-- The exact network cancels for every input, even outside this box. -/
theorem exact_cancellation (x : Fin 1 → ℝ) : predict W b v 0 x = 0 := by
  simp [predict,LinearModelInference.predict,IntervalDotProduct.dot,
    Fin.sum_univ_succ,v,activations,W,b]

/-- Each neuron attains both marginal endpoints, but not arbitrary combinations. -/
theorem individual_endpoints (j : Fin 2) :
    activations W b (fun _ => 0) j = 0 ∧ activations W b (fun _ => 1) j = 1 := by
  norm_num [activations,relu,LinearModelInference.predict,IntervalDotProduct.dot,
    Fin.sum_univ_succ,W,b]

theorem output_sound {x : Fin 1 → ℝ} (hx : IntervalDotProduct.InBox I x) :
    (bounds W b v 0 I).Contains (predict W b v 0 x) := sound W b v 0 hx

theorem endpoints_unattained :
    (¬∃ x, IntervalDotProduct.InBox I x ∧ predict W b v 0 x = ((bounds W b v 0 I).lo : ℝ)) ∧
    (¬∃ x, IntervalDotProduct.InBox I x ∧ predict W b v 0 x = ((bounds W b v 0 I).hi : ℝ)) := by
  constructor
  · rintro ⟨x,_,h⟩; rw [exact_cancellation,output_bounds.1] at h; norm_num at h
  · rintro ⟨x,_,h⟩; rw [exact_cancellation,output_bounds.2] at h; norm_num at h

/-- The independent box contains a hidden vector no shared input can produce. -/
def spurious : Fin 2 → ℝ := ![0,1]

theorem spurious_in_box : IntervalDotProduct.InBox (hiddenBounds W b I) spurious := by
  intro j
  constructor
  · rw [hidden_bounds j |>.1]
    fin_cases j <;> norm_num [spurious]
  · rw [hidden_bounds j |>.2]
    fin_cases j <;> norm_num [spurious]

theorem spurious_unreachable : ¬ ∃ x, activations W b x = spurious := by
  rintro ⟨x,h⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have he : activations W b x 0 = activations W b x 1 := rfl
  simp [spurious] at h0 h1
  linarith

theorem negative_clip : (reluBounds ⟨-2,-1,by norm_num⟩).lo = 0 ∧
    (reluBounds ⟨-2,-1,by norm_num⟩).hi = 0 := by norm_num [reluBounds]
theorem zero_boundary : relu 0 = 0 := by simp [relu]
theorem crossing_clip : (reluBounds ⟨-1,2,by norm_num⟩).lo = 0 ∧
    (reluBounds ⟨-1,2,by norm_num⟩).hi = 2 := by norm_num [reluBounds]

/-- A single neuron control with nonzero hidden and output biases. -/
def oneW : Fin 1 → Fin 1 → ℚ := fun _ _ => 2
def oneB : Fin 1 → ℚ := fun _ => -1
def oneV : Fin 1 → ℚ := fun _ => 3
def oneI : Fin 1 → QInterval := fun _ => ⟨0,1,by norm_num⟩

theorem biased_bounds : (bounds oneW oneB oneV 1 oneI).lo = 1 ∧
    (bounds oneW oneB oneV 1 oneI).hi = 4 := by
  norm_num [bounds,hiddenBounds,reluBounds,LinearModelInference.bounds,
    IntervalDotProduct.weightedBounds,IntervalDotProduct.bounds,QInterval.add,
    QInterval.point,QInterval.mul,Fin.sum_univ_succ,oneW,oneB,oneV,oneI]

theorem biased_threshold {x : Fin 1 → ℝ} (hx : IntervalDotProduct.InBox oneI x) :
    0 < predict oneW oneB oneV 1 x := by
  have h := (sound oneW oneB oneV 1 hx).1
  rw [biased_bounds.1] at h
  exact lt_of_lt_of_le zero_lt_one (by simpa using h)

theorem biased_attained : predict oneW oneB oneV 1 (fun _ => 0) = 1 ∧
    predict oneW oneB oneV 1 (fun _ => 1) = 4 := by
  norm_num [predict,activations,relu,LinearModelInference.predict,IntervalDotProduct.dot,
    Fin.sum_univ_succ,oneW,oneB,oneV]

theorem no_hidden (W : Fin 0 → Fin 1 → ℚ) (b v : Fin 0 → ℚ) (c : ℚ) (x : Fin 1 → ℝ) :
    predict W b v c x = c := by simp [predict,LinearModelInference.predict,IntervalDotProduct.dot]

#eval ((bounds W b v 0 I).lo,(bounds W b v 0 I).hi)
#eval ((bounds oneW oneB oneV 1 oneI).lo,(bounds oneW oneB oneV 1 oneI).hi)
end GeneralizedIntervalArithmetic.ReluNetworkInferenceChecks
#audit_namespace GeneralizedIntervalArithmetic.ReluNetworkInferenceChecks
