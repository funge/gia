import Mathlib.Data.Real.Irrational
import ContinuedFractionConversion
import AuditPolicy
import Mathlib.Tactic.NormNum
namespace GeneralizedIntervalArithmetic.ContinuedFractionConversionChecks
open ContinuedFractionConversion

theorem rational_roundtrip : recover (43/19) = 43/19 := recover_exact _

theorem early_convergent_is_not_exact :
    (GenContFract.of (43/19 : ℚ)).convs 0 = 2 ∧
    (GenContFract.of (43/19 : ℚ)).convs 0 ≠ 43/19 := by
  norm_num [GenContFract.zeroth_conv_eq_h, GenContFract.of_h_eq_floor]

theorem zero_boundary : cutoff 0 = 1 ∧ recover 0 = 0 ∧
    GenContFract.IntFractPair.stream (0:ℚ) 1 = none := by
  have hc : cutoff 0 = 1 := by norm_num [cutoff]
  exact ⟨hc, recover_exact _, by simpa [hc] using stream_stopped 0⟩

theorem integer_boundary : cutoff 7 = 1 ∧ recover 7 = 7 := by
  exact ⟨by norm_num [cutoff, Int.fract], recover_exact _⟩

/-- Signed rational extension of the positive source representation. -/
theorem negative_control : recover (-43/19) = -43/19 := recover_exact _

/-- Finite truncation is not evidence that the constructed real expansion ends. -/
theorem nonrational_does_not_terminate (x : ℝ)
    (h : ¬ ∃ q : ℚ, x = (q:ℝ)) : ¬ (GenContFract.of x).Terminates :=
  fun ht => h ((finite_iff_rational x).mp ht)

/-- The source's final-term restriction matters: allowing a trailing 1
admits two distinct finite coefficient presentations of the same value.
This arithmetic witness is not a general normalization theorem. -/
theorem trailing_one_ambiguity :
    (1 + 1/(2:ℚ)) = 1 + 1/(1 + 1/(1:ℚ)) := by norm_num

/-- Public representation contains a last denominator 2, as required. -/
theorem constructed_last_two : (GenContFract.of (3/2:ℚ)).s.get? 0 = some ⟨1,2⟩ := by
  apply GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream
    (ifp_succ_n := ⟨2,0⟩)
  rw [GenContFract.IntFractPair.stream_succ_of_some
    (GenContFract.IntFractPair.stream_zero (3/2:ℚ))
    (by norm_num [GenContFract.IntFractPair.of, Int.fract])]
  norm_num [GenContFract.IntFractPair.of, Int.fract]

/-- Distinct actual finite presentations, same value, with terminal 1 forbidden
by the constructed form's theorem. -/
theorem actual_terminal_one_ambiguity :
    finitePresentation 1 [1,1] ≠ finitePresentation 1 [2] ∧
    (finitePresentation 1 [1,1]).convs' 2 = (finitePresentation 1 [2]).convs' 1 ∧
    (finitePresentation 1 [2]).convs' 1 = recover (3/2) := by
  refine ⟨?_, by convert terminal_one_contraction 1 1 le_rfl using 1; norm_num, ?_⟩
  · intro h
    have hh := congrArg (fun g : GenContFract ℚ => g.s.get? 0) h
    norm_num [finitePresentation, Stream'.Seq.ofList_get?] at hh
  · rw [recover_exact]
    norm_num [finitePresentation, GenContFract.convs', GenContFract.convs'Aux,
      Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]

theorem recovery_preserves_constructed_form (q : ℚ) :
    GenContFract.of (recover q) = GenContFract.of q :=
  (constructed_injective _ _).mpr (recover_exact q)

theorem arbitrary_prefix_control :
    finiteValue 0 [2,3,4,1] = finiteValue 0 [2,3,5] := by
  convert prefix_terminal_one 0 4 [2,3] using 1; norm_num

theorem normalized_reconstruction_control :
    GenContFract.of (finiteValue 0 [2,1,3]) = finitePresentation 0 [2,1,3] := by
  simpa using reconstruct_normalized 0 [2,1,3] (by norm_num [Normalized])

theorem singleton_reconstruction_control :
    GenContFract.of (finiteValue 1 []) = finitePresentation 1 [] := by
  simpa using reconstruct_normalized 1 [] trivial

theorem noncanonical_recomputes :
    GenContFract.of (finiteValue 1 [1,1]) = finitePresentation 1 [2] := by
  have he : finiteValue 1 [1,1] = finiteValue 1 [2] := by
    convert prefix_terminal_one 1 1 [] using 1; norm_num
  rw [he]
  simpa using reconstruct_normalized 1 [2] (by norm_num [Normalized])

theorem validity_controls :
    ¬ Normalized [2,0] ∧ ¬ Normalized [2,1] ∧ Normalized [2,1,3] ∧
    1 ≤ finiteValue 2 [1] := by
  refine ⟨by norm_num [Normalized], by norm_num [Normalized],
    by norm_num [Normalized], ?_⟩
  simpa using positive_tail_value 2 [1] (by norm_num) (by simp)

open Filter
open scoped Topology

private theorem sqrt_two_not_rational : ¬ ∃ q : ℚ, Real.sqrt 2 = (q:ℝ) := by
  rintro ⟨q,hq⟩
  exact irrational_sqrt_two ⟨q,hq.symm⟩

/-- Infinite canonical expansion converges but no finite truncation is exact. -/
theorem sqrt_two_control :
    Tendsto (GenContFract.of (Real.sqrt 2)).convs atTop (𝓝 (Real.sqrt 2)) ∧
    (∀ n, (GenContFract.of (Real.sqrt 2)).s.get? n ≠ none) ∧
    (∀ n, (GenContFract.of (Real.sqrt 2)).convs n ≠ Real.sqrt 2) :=
  ⟨canonical_converges _,irrational_entry_present _ sqrt_two_not_rational,
    irrational_no_exact_truncation _ sqrt_two_not_rational⟩

theorem converted_stream_no_false_limit :
    SequenceRepresentations.Represents (rationalConvergent (Real.sqrt 2)) (Real.sqrt 2) ∧
    ¬ SequenceRepresentations.Represents (rationalConvergent (Real.sqrt 2)) 2 := by
  refine ⟨rational_stream_represents _, ?_⟩
  intro h
  exact sqrt_two_not_rational ⟨2,by simpa using rational_stream_unique _ _ h⟩

theorem irrational_accuracy_control :
    ∃ N : ℕ, ∀ n ≥ N, |Real.sqrt 2 - (GenContFract.of (Real.sqrt 2)).convs n| < 1/1000 :=
  canonical_accuracy _ _ (by norm_num)

theorem rational_boundary_control :
    ∀ᶠ n in atTop, rationalConvergent 0 n = 0 := by
  simpa using rational_stream_eventually_exact 0

#eval recover (43/19)
end GeneralizedIntervalArithmetic.ContinuedFractionConversionChecks
#audit_namespace GeneralizedIntervalArithmetic.ContinuedFractionConversionChecks
