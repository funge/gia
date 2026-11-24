import ExpressionStreams

namespace GeneralizedIntervalArithmetic.AccuracySearchExample
open ExpressionStreams Filter
open scoped Topology

/-- Deliberately rejected for two stages, then exact. -/
def input (n : ℕ) : QInterval := if n < 2 then ⟨0,2,by norm_num⟩ else .point 1

theorem input_converges : Converges input 1 := by
  have he : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  constructor
  · apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).congr'
    filter_upwards [he] with n hn
    simp [input,not_lt_of_ge hn,QInterval.point]
  · apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).congr'
    filter_upwards [he] with n hn
    simp [input,not_lt_of_ge hn,QInterval.point]

def nested : Expr := .div (.const 1) (.div .x (.const 2))
theorem nested_value : Value 1 0 nested 2 := by
  have h := Value.div (Value.const (x:=1) (y:=0) 1)
    (Value.div Value.x (Value.const 2) (by norm_num)) (by norm_num : (1:ℝ)/2 ≠ 0)
  norm_num at h
  exact h

def selected : Nat := firstPrecision input (fun _ => .point 0) nested input_converges
  (by simpa using point_converges 0) nested_value (1/100) (by norm_num)

theorem input_contains (n : ℕ) : (input n).Contains 1 := by
  unfold input
  split <;> norm_num [QInterval.Contains,QInterval.point]

theorem selected_certificate :
    ∃ I, eval exactBackend (input selected) (.point 0) nested = some I ∧
      I.Contains 2 ∧ ∀ w, I.Contains w → |w-2| < (1/100:ℝ) := by
  simpa [selected] using firstPrecision_certificate input (fun _ => QInterval.point 0)
    nested input_converges (by simpa using point_converges 0) nested_value input_contains
    (fun _ => by norm_num [QInterval.point,QInterval.Contains]) (1/100) (by norm_num)

end GeneralizedIntervalArithmetic.AccuracySearchExample
