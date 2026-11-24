import InfinityStreams
import AuditPolicy

namespace GeneralizedIntervalArithmetic.InfinityStreamsChecks
open InfinityStreams Filter
open scoped Topology

theorem positive_integer : Represents (fun k : ℤ => (k : ℚ)) .posInf := integer_stream

theorem negative_integer : Represents (fun k : ℤ => -(k : ℚ)) .negInf :=
  (down_neg_iff _).mpr integer_stream

theorem constant_finite (q : ℚ) : Represents (fun _ : ℤ => q) (.finite q) :=
  tendsto_const_nhds

theorem finite_not_infinite (q : ℚ) : ¬ Represents (fun _ : ℤ => q) .posInf := by
  intro h
  have := representation_unique (constant_finite q) h
  cases this

theorem infinity_representation_not_numerical_equality :
    Represents (fun k : ℤ => (k : ℚ)) .posInf ∧
    ExceptionalComparisons.observe .eq .posInf .posInf = some false := ⟨integer_stream, rfl⟩

def changedPrefix (k : ℤ) : ℚ := if k ≤ 10 then 0 else k

theorem prefix_irrelevant : Up changedPrefix := by
  have he : changedPrefix =ᶠ[atTop] (fun k : ℤ => (k : ℚ)) :=
    eventually_atTop.2 ⟨11, fun k hk => by simp [changedPrefix, show ¬ k ≤ 10 by omega]⟩
  exact (eventual_agreement he).1.mpr integer_stream

/-- A divergent sequence need not be monotone (it drops from 3 to 2). -/
def saw (k : ℤ) : ℚ := (k : ℚ) + 2*((k % 2 : ℤ) : ℚ)

theorem saw_diverges : Up saw := by
  intro l
  obtain ⟨j, hj⟩ := integer_stream l
  refine ⟨j, fun k hk => ?_⟩
  have hh := hj k hk
  have hz : (0 : ℚ) ≤ (k % 2 : ℤ) := by exact_mod_cast (Int.emod_nonneg k (by norm_num : (2 : ℤ) ≠ 0))
  dsimp [saw] at *
  linarith

theorem saw_not_monotone : ¬ Monotone saw := by
  intro h
  have := h (show (1 : ℤ) ≤ 2 by norm_num)
  norm_num [saw] at this

theorem every_tail_unbounded_but_no_signed_divergence :
    (∀ l j, ∃ k, j < k ∧ l < spikes k) ∧
    ¬ BddAbove (Set.range spikes) ∧ ¬ Up spikes ∧ ¬ Down spikes :=
  ⟨spikes_tail_unbounded, spikes_unbounded, spikes_not_up, spikes_not_down⟩

theorem no_infinite_limit_for_spikes :
    ¬ Tendsto (fun k => ((spikes k : ℝ) : EReal)) atTop (𝓝 ⊤) ∧
    ¬ Tendsto (fun k => ((spikes k : ℝ) : EReal)) atTop (𝓝 ⊥) :=
  ⟨fun h => spikes_not_up ((up_iff_extended_limit _).mpr h),
   fun h => spikes_not_down ((down_iff_extended_limit _).mpr h)⟩

theorem zero_subsequence (k : ℤ) : spikes (2*k+1) = 0 := by
  have hm : (2*k+1) % 2 ≠ 0 := by omega
  simp [spikes, hm]

theorem strict_cutoff_is_not_inclusive :
    (∀ k : ℤ, 0 < k → (0 : ℚ) < k) ∧ ¬ ((0 : ℚ) < (0 : ℤ)) := by
  constructor
  · intro k hk
    exact_mod_cast hk
  · norm_num

theorem lambda_not_a_limit_tag :
    ¬ Represents (fun k : ℤ => (k : ℚ)) .undefined ∧
    ExceptionalComparisons.bound .undefined = none := undefined_not_promoted _

end GeneralizedIntervalArithmetic.InfinityStreamsChecks
#audit_namespace GeneralizedIntervalArithmetic.InfinityStreamsChecks
