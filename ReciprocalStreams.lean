import Intervals
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.GroupWithZero

namespace GeneralizedIntervalArithmetic.ReciprocalStreams
open Filter
open scoped Topology

/-- Guarded real interval reciprocal, not Lean's totalized inverse at zero. -/
noncomputable def evaluate (l u : ℝ) : Option (ℝ × ℝ) :=
  if l ≤ u ∧ (0 < l ∨ u < 0) then some (1/u,1/l) else none

theorem evaluate_sound {l u a b x : ℝ} (h : evaluate l u = some (a,b))
    (hx : x ∈ Set.Icc l u) : x ≠ 0 ∧ x ∈ Set.Icc l u ∧ 1/x ∈ Set.Icc a b := by
  unfold evaluate at h
  split_ifs at h with hg
  · cases h
    rcases hg.2 with hp | hn
    · have hp' : 0 < x := lt_of_lt_of_le hp hx.1
      exact ⟨ne_of_gt hp',hx,one_div_le_one_div_of_le hp' hx.2,
        one_div_le_one_div_of_le hp hx.1⟩
    · have hn' : x < 0 := lt_of_le_of_lt hx.2 hn
      exact ⟨ne_of_lt hn',hx,one_div_le_one_div_of_neg_of_le hn hx.2,
        one_div_le_one_div_of_neg_of_le hn' hx.1⟩

/-- Convergence to a nonzero limit eventually discharges the guard. Ordering is
supplied independently; convergence alone does not order endpoints. -/
theorem eventually_success {l u : ℕ → ℝ} {r : ℝ}
    (hl : Tendsto l atTop (𝓝 r)) (hu : Tendsto u atTop (𝓝 r)) (hr : r ≠ 0)
    (ho : ∀ n, l n ≤ u n) :
    ∀ᶠ n in atTop, evaluate (l n) (u n) = some (1/u n,1/l n) := by
  rcases lt_or_gt_of_ne hr with hn | hp
  · filter_upwards [hu.eventually_lt_const hn] with n h
    simp [evaluate,ho n,h]
  · filter_upwards [hl.eventually_const_lt hp] with n h
    simp [evaluate,ho n,h]

/-- The two eventual output endpoints converge to the reciprocal. This proves
no computable modulus or success at all stages. Nestedness is not needed. -/
theorem converges {l u : ℕ → ℝ} {r : ℝ}
    (hl : Tendsto l atTop (𝓝 r)) (hu : Tendsto u atTop (𝓝 r)) (hr : r ≠ 0)
    (ho : ∀ n, l n ≤ u n) :
    (∀ᶠ n in atTop, evaluate (l n) (u n) = some (1/u n,1/l n)) ∧
    Tendsto (fun n => 1/u n) atTop (𝓝 (1/r)) ∧
    Tendsto (fun n => 1/l n) atTop (𝓝 (1/r)) := by
  exact ⟨eventually_success hl hu hr ho,
    by simpa [one_div] using hu.inv₀ hr,
    by simpa [one_div] using hl.inv₀ hr⟩

/-- Every actual value has the same-index witness; no value is created at zero. -/
theorem eventual_enclosure {l u : ℕ → ℝ} {r : ℝ}
    (hl : Tendsto l atTop (𝓝 r)) (hu : Tendsto u atTop (𝓝 r)) (hr : r ≠ 0)
    (ho : ∀ n, l n ≤ u n) :
    ∀ᶠ n in atTop, ∀ x ∈ Set.Icc (l n) (u n),
      x ≠ 0 ∧ 1/x ∈ Set.Icc (1/u n) (1/l n) := by
  filter_upwards [eventually_success hl hu hr ho] with n hn
  intro x hx
  have h := evaluate_sound hn hx
  exact ⟨h.1,h.2.2⟩

end GeneralizedIntervalArithmetic.ReciprocalStreams
