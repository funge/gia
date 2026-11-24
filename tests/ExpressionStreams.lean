import ExpressionStreams
import AuditPolicy
import Mathlib.Analysis.SpecificLimits.Basic

namespace GeneralizedIntervalArithmetic.ExpressionStreamsChecks
open ExpressionStreams Filter
open scoped Topology

def radius (n : ℕ) : ℚ := 1/(n+1)
theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity

def aroundOne (n : ℕ) : QInterval :=
  ⟨1-radius n,1+radius n,by linarith [radius_pos n]⟩
def aroundZero (n : ℕ) : QInterval :=
  ⟨-radius n,radius n,by linarith [radius_pos n]⟩

theorem radius_converges : Tendsto (fun n => (radius n : ℝ)) atTop (𝓝 0) := by
  simpa [radius] using tendsto_one_div_add_atTop_nhds_zero_nat

theorem one_converges : Converges aroundOne 1 := by
  constructor
  · simpa [aroundOne] using
      (tendsto_const_nhds.sub radius_converges :
        Tendsto (fun n => (1:ℝ)-(radius n:ℝ)) atTop (𝓝 (1-0)))
  · simpa [aroundOne] using
      (tendsto_const_nhds.add radius_converges :
        Tendsto (fun n => (1:ℝ)+(radius n:ℝ)) atTop (𝓝 (1+0)))

theorem zero_converges : Converges aroundZero 0 := by
  exact ⟨by simpa [aroundZero] using radius_converges.neg, radius_converges⟩

theorem one_enclosed (n : ℕ) : (aroundOne n).Contains 1 := by
  have h : (0:ℝ) ≤ radius n := by exact_mod_cast le_of_lt (radius_pos n)
  simp only [QInterval.Contains,aroundOne,Rat.cast_sub,Rat.cast_add,Rat.cast_one]
  constructor <;> linarith

def nested : Expr := .div (.const 1) (.div .x (.const 2))
theorem nested_value : Value 1 0 nested 2 := by
  have h := Value.div (Value.const (x:=1) (y:=0) 1)
    (Value.div Value.x (Value.const 2) (by norm_num)) (by norm_num : (1:ℝ)/2 ≠ 0)
  norm_num at h
  exact h

theorem nested_initial_failure : eval exactBackend (aroundOne 0) (.point 0) nested = none := by
  change combine (some (.point 1))
    (eval exactBackend (aroundOne 0) (.point 0) (.div .x (.const 2))) (guardedDiv exactBackend) = none
  cases he : eval exactBackend (aroundOne 0) (.point 0) (.div .x (.const 2)) with
  | none => rfl
  | some J =>
    have hv : Value 0 0 (.div .x (.const 2)) 0 := by
      simpa using Value.div (Value.x (x:=0) (y:=0)) (Value.const 2) (by norm_num : (2:ℝ) ≠ 0)
    have hz := eval_sound exactBackend_sound
      (show (aroundOne 0).Contains 0 by norm_num [aroundOne,radius,QInterval.Contains])
      (show (QInterval.point 0).Contains 0 by norm_num [QInterval.point,QInterval.Contains]) hv J he
    exact guardedDiv_zero_unknown exactBackend (.point 1) J
      ⟨by exact_mod_cast hz.1,by exact_mod_cast hz.2⟩

theorem nested_eventual_accuracy :
    ∀ᶠ n in atTop, precisionTest (1/100) (eval exactBackend (aroundOne n) (.point 0) nested) = true :=
  eventually_precision one_converges (by simpa using point_converges 0) nested_value (by norm_num)

def allOps : Expr := .div (.add (.sub (.mul .x .x) .y) (.const 1)) (.add .x .y)
theorem all_ops_value : Value 1 1 allOps (1/2) := by
  have h := Value.div (Value.add (Value.sub (Value.mul (Value.x (x:=1) (y:=1)) Value.x)
    Value.y) (Value.const 1)) (Value.add Value.x Value.y) (by norm_num : (1:ℝ)+1 ≠ 0)
  norm_num at h
  exact h

theorem all_ops_converge :
    ∃ R, Converges R (1/2) ∧ ∀ᶠ n in atTop,
      eval exactBackend (aroundOne n) (.point 1) allOps = some (R n) :=
  eval_converges one_converges (by simpa using point_converges 1) all_ops_value

theorem correlated_subtraction :
    ∀ᶠ n in atTop, precisionTest (1/100)
      (eval exactBackend (aroundOne n) (.point 0) (.sub .x .x)) = true := by
  apply eventually_precision one_converges (by simpa using point_converges 0)
    (show Value 1 0 (.sub .x .x) 0 from by simpa using Value.sub (Value.x (x:=1) (y:=0)) Value.x)
  norm_num

theorem pole_always_rejected (n : ℕ) :
    eval exactBackend (aroundZero n) (.point 0) (.div (.const 1) .x) = none := by
  have hr := le_of_lt (radius_pos n)
  simp [eval,combine,exactBackend,guardedDiv,QInterval.AwayZero,aroundZero,
    not_lt_of_ge hr,not_lt_of_ge (neg_nonpos.mpr hr)]

theorem pole_has_no_value (z : ℝ) : ¬ Value 0 0 (.div (.const 1) .x) z := by
  intro h
  cases h with
  | div ha hb hn => cases hb; exact hn rfl

theorem zero_times_pole_has_no_value (z : ℝ) :
    ¬ Value 0 0 (.mul (.const 0) (.div (.const 1) .x)) z := by
  intro h
  cases h with
  | mul ha hb => exact pole_has_no_value _ hb

theorem zero_times_pole_rejected (n : ℕ) :
    eval exactBackend (aroundZero n) (.point 0) (.mul (.const 0) (.div (.const 1) .x)) = none := by
  change combine (some (.point 0))
    (eval exactBackend (aroundZero n) (.point 0) (.div (.const 1) .x)) _ = none
  rw [pole_always_rejected]
  rfl

theorem convergence_not_containment :
    Converges (fun n => QInterval.point (radius n)) 0 ∧
    ∀ n, ¬ (QInterval.point (radius n)).Contains 0 := by
  refine ⟨⟨radius_converges,radius_converges⟩,?_⟩
  intro n h
  have hp : (0:ℝ) < radius n := by exact_mod_cast radius_pos n
  exact not_le_of_gt hp h.1

theorem stopping_boundary :
    precisionTest 1 (some ⟨0,1,by norm_num⟩) = false ∧
    precisionTest 0 (some (.point 0)) = false ∧ precisionTest 1 none = false := by
  norm_num [precisionTest,QInterval.point]

theorem pole_still_has_defined_values (n : ℕ) :
    ∃ a v : ℝ, (aroundZero n).Contains a ∧ Value a 0 (.div (.const 1) .x) v := by
  have hp : (0:ℝ) < radius n := by exact_mod_cast radius_pos n
  refine ⟨radius n,1/(radius n:ℝ),?_,?_⟩
  · simp only [QInterval.Contains,aroundZero,Rat.cast_neg]
    constructor <;> linarith
  · simpa using Value.div (Value.const (x:=(radius n:ℝ)) (y:=0) 1) Value.x (ne_of_gt hp)

theorem constant_search_zero :
    firstPrecision (fun _ => QInterval.point 1) (fun _ => QInterval.point 0) (.const 2)
      (point_converges 1) (point_converges 0) (Value.const 2) 1 (by norm_num) = 0 := by
  apply (Nat.find_eq_iff _).mpr
  constructor
  · norm_num [precisionTest,eval,exactBackend,QInterval.point]
  · intro n hn; omega


end GeneralizedIntervalArithmetic.ExpressionStreamsChecks
#audit_namespace GeneralizedIntervalArithmetic.ExpressionStreamsChecks
