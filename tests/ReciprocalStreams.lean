import ReciprocalStreams
import AuditPolicy
import Mathlib.Analysis.SpecificLimits.Basic
namespace GeneralizedIntervalArithmetic.ReciprocalStreamsChecks
open ReciprocalStreams Filter
open scoped Topology

theorem positive_stage : evaluate 1 2 = some ((1/2:ℝ),1) := by norm_num [evaluate]
theorem negative_stage : evaluate (-2) (-1) = some ((-1:ℝ),-1/2) := by norm_num [evaluate]
theorem touching_rejected : evaluate 0 1 = none ∧ evaluate (-1) 0 = none := by
  norm_num [evaluate]
theorem reversed_rejected : evaluate 2 1 = none := by norm_num [evaluate]

theorem nonzero_constant_stream :
    ∀ᶠ _n : ℕ in atTop, evaluate 2 2 = some ((1/2:ℝ),1/2) :=
  eventually_success tendsto_const_nhds tendsto_const_nhds (by norm_num) (fun _ => le_rfl)

/-- Dropping the nonzero-limit premise would assert success on this stream. -/
theorem zero_limit_falsifier :
    Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0) ∧
    (∀ _n : ℕ, evaluate 0 0 = none) ∧
    ¬ (∀ᶠ _n : ℕ in atTop, evaluate 0 0 = some ((0:ℝ),0)) := by
  refine ⟨tendsto_const_nhds,fun _ => ?_,?_⟩
  · norm_num [evaluate]
  · simp only [evaluate, lt_self_iff_false, or_self, and_false, ↓reduceIte, reduceCtorEq]
    exact not_eventually.mpr (Frequently.of_forall (fun _ => id))
noncomputable def lower (n : ℕ) : ℝ := 1 - 1/(n+1)
noncomputable def upper (n : ℕ) : ℝ := 1 + 1/(n+1)

theorem shrinking_stream :
    (evaluate (lower 0) (upper 0) = none) ∧
    (∀ᶠ n in atTop, evaluate (lower n) (upper n) = some (1/upper n,1/lower n)) ∧
    Tendsto (fun n => 1/upper n) atTop (𝓝 1) ∧
    Tendsto (fun n => 1/lower n) atTop (𝓝 1) := by
  have hl : Tendsto lower atTop (𝓝 1) := by
    simpa only [lower, sub_zero] using (tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1:ℝ)-1/(n+1)) atTop (𝓝 (1-0)))
  have hu : Tendsto upper atTop (𝓝 1) := by
    simpa only [upper, add_zero] using (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1:ℝ)+1/(n+1)) atTop (𝓝 (1+0)))
  have ho : ∀ n, lower n ≤ upper n := by
    intro n
    have h : (0:ℝ) ≤ 1/(n+1) := by positivity
    dsimp [lower,upper]; linarith
  exact ⟨by norm_num [evaluate,lower,upper], by simpa using converges hl hu (by norm_num) ho⟩

end GeneralizedIntervalArithmetic.ReciprocalStreamsChecks
#audit_namespace GeneralizedIntervalArithmetic.ReciprocalStreamsChecks
