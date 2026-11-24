import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import SequenceRepresentations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Data.Real.Archimedean

/-! Tupper §2.15.4: finite rational conversion through mathlib's actual
floor/fraction reciprocal construction. No new continued-fraction evaluator. -/
namespace GeneralizedIntervalArithmetic.ContinuedFractionConversion

/-- Conservative bound on the decreasing fractional-part numerator. -/
def cutoff (q : ℚ) : ℕ := (Int.fract q).num.natAbs + 1

/-- Finite observation of the actual constructed continued fraction. -/
def recover (q : ℚ) : ℚ := (GenContFract.of q).convs (cutoff q - 1)

/-- The construction has stopped by this explicit bound, not merely some
classically chosen index. -/
theorem stream_stopped (q : ℚ) :
    GenContFract.IntFractPair.stream q (cutoff q) = none := by
  cases h : GenContFract.IntFractPair.stream q (cutoff q) with
  | none => rfl
  | some p =>
    have hle := GenContFract.IntFractPair.stream_nth_fr_num_le_fr_num_sub_n_rat h
    have hp : 0 ≤ p.fr.num := Rat.num_nonneg.mpr
      (GenContFract.IntFractPair.nth_stream_fr_nonneg_lt_one h).1
    have hq : 0 ≤ (Int.fract q).num := Rat.num_nonneg.mpr (Int.fract_nonneg q)
    have he : (GenContFract.IntFractPair.of q).fr = Int.fract q := rfl
    rw [he] at hle
    simp only [cutoff, Nat.cast_add, Nat.cast_one, Int.natAbs_of_nonneg hq] at hle
    omega

theorem recover_exact (q : ℚ) : recover q = q :=
  (GenContFract.of_correctness_of_nth_stream_eq_none (stream_stopped q)).symm

theorem real_recovery (q : ℚ) : (recover q : ℝ) = (q : ℝ) := by
  rw [recover_exact]

/-- Source rational-iff-finite correspondence, for the constructed real expansion.
This is not uniqueness of arbitrary normalized coefficient lists. -/
theorem finite_iff_rational (x : ℝ) :
    (GenContFract.of x).Terminates ↔ ∃ q : ℚ, x = (q : ℝ) :=
  GenContFract.terminates_iff_rat x

/-- Rational-to-real promotion preserves the constructed head and every pair,
not only the final represented value. -/
theorem promote (q : ℚ) :
    (⟨((GenContFract.of q).h : ℝ),
      (GenContFract.of q).s.map (GenContFract.Pair.map (fun r : ℚ => (r : ℝ)))⟩ :
        GenContFract ℝ) = GenContFract.of (q : ℝ) :=
  GenContFract.coe_of_rat_eq rfl

theorem eventually_exact (q : ℚ) :
    ∀ᶠ n in Filter.atTop, (GenContFract.of q).convs n = q :=
  (GenContFract.of_correctness_atTop_of_terminates
    (GenContFract.terminates_of_rat q)).mono (fun _ h => h.symm)

/-- A final non-initial coefficient of the actual construction is at least 2.
The strict bound comes from inverting a nonzero fractional part below 1. -/
theorem terminal_coefficient {q : ℚ} {n : ℕ}
    {p : GenContFract.IntFractPair ℚ}
    (hp : GenContFract.IntFractPair.stream q (n+1) = some p)
    (ht : GenContFract.IntFractPair.stream q (n+2) = none) : 2 ≤ p.b := by
  have hz : p.fr = 0 := by
    rcases GenContFract.IntFractPair.succ_nth_stream_eq_none_iff.mp ht with h | ⟨r,hr,hz⟩
    · rw [hp] at h; contradiction
    · have he : r = p := Option.some.inj (hr.symm.trans hp)
      simpa [he] using hz
  obtain ⟨r,hr,hn,he⟩ := GenContFract.IntFractPair.succ_nth_stream_eq_some_iff.mp hp
  have hpos : 0 < r.fr := lt_of_le_of_ne
    (GenContFract.IntFractPair.nth_stream_fr_nonneg hr) (Ne.symm hn)
  have hlt := GenContFract.IntFractPair.nth_stream_fr_lt_one hr
  have hinv : (1:ℚ) < r.fr⁻¹ := (one_lt_inv₀ hpos).mpr hlt
  have hzero : Int.fract r.fr⁻¹ = 0 := by rw [← he] at hz; exact hz
  have heq : r.fr⁻¹ = (⌊r.fr⁻¹⌋ : ℚ) := by
    simpa only [Int.fract, sub_eq_zero] using hzero
  have hb : 1 < p.b := by
    have hc : (1:ℚ) < (p.b : ℚ) := by
      rw [← he]; change (1:ℚ) < (⌊r.fr⁻¹⌋ : ℚ); rwa [← heq]
    exact_mod_cast hc
  omega

/-- The final stored denominator pair, in the public continued-fraction API. -/
theorem final_pair_ge_two {q : ℚ} {n : ℕ} {p : GenContFract.Pair ℚ}
    (hp : (GenContFract.of q).s.get? n = some p)
    (ht : (GenContFract.of q).s.get? (n+1) = none) : 2 ≤ p.b := by
  obtain ⟨r,hr,hb⟩ := GenContFract.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some hp
  have hs : GenContFract.IntFractPair.stream q (n+2) = none :=
    GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mp ht
  have h := terminal_coefficient hr hs
  rw [← hb]
  exact_mod_cast h

/-- A coefficient 1 can occur internally, but cannot terminate the expansion. -/
theorem one_not_terminal {q : ℚ} {n : ℕ}
    {p : GenContFract.IntFractPair ℚ}
    (hp : GenContFract.IntFractPair.stream q (n+1) = some p) (h1 : p.b = 1) :
    GenContFract.IntFractPair.stream q (n+2) ≠ none := by
  intro ht
  have := terminal_coefficient hp ht
  omega

/-- Uniqueness among expansions produced by the actual rational constructor.
Not a classification of arbitrary normalized lists or infinite presentations. -/
theorem constructed_injective (q r : ℚ) : GenContFract.of q = GenContFract.of r ↔ q = r := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := GenContFract.terminates_of_rat q
    have hr : (GenContFract.of r).TerminatedAt n := h ▸ hn
    rw [GenContFract.of_correctness_of_terminatedAt hn,
      GenContFract.of_correctness_of_terminatedAt hr, h]
  · rintro rfl; rfl

/-- Finite input in the library's real representation, not a parallel evaluator. -/
def finitePresentation (a : ℚ) (bs : List ℚ) : GenContFract ℚ :=
  ⟨a, Stream'.Seq.ofList (bs.map (fun b => ⟨1,b⟩))⟩

/-- Local terminal-1 contraction on the actual finite representation. The
positive denominator premise records the source admissible tail domain. -/
theorem terminal_one_contraction (a b : ℚ) (_hb : 1 ≤ b) :
    (finitePresentation a [b,1]).convs' 2 =
    (finitePresentation a [b+1]).convs' 1 := by
  simp [finitePresentation, GenContFract.convs', GenContFract.convs'Aux,
    Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]

/-- Decode the whole finite presentation using the library evaluator. -/
def finiteValue (a : ℚ) (bs : List ℚ) : ℚ :=
  (finitePresentation a bs).convs' bs.length

theorem finiteValue_nil (a : ℚ) : finiteValue a [] = a := by
  simp [finiteValue, finitePresentation, GenContFract.convs', GenContFract.convs'Aux]

theorem finiteValue_cons (a b : ℚ) (bs : List ℚ) :
    finiteValue a (b::bs) = a + 1 / finiteValue b bs := by
  simp [finiteValue, finitePresentation, GenContFract.convs', GenContFract.convs'Aux,
    Stream'.Seq.ofList_cons]

/-- Terminal-1 contraction through every prefix, using the actual evaluator.
This identity is algebraic; positive-tail validity is checked separately. -/
theorem prefix_terminal_one (a b : ℚ) (pre : List ℚ) :
    finiteValue a (pre ++ [b,1]) = finiteValue a (pre ++ [b+1]) := by
  induction pre generalizing a with
  | nil => simp [finiteValue_cons, finiteValue_nil]
  | cons c cs ih =>
    simp only [List.cons_append, finiteValue_cons]
    rw [ih]

/-- Integral positive tails with the source final-term convention. Head integers
are unconstrained; restrict the head to nonnegative for the positive source. -/
def Normalized : List ℤ → Prop
  | [] => True
  | [b] => 2 ≤ b
  | b::c::cs => 1 ≤ b ∧ Normalized (c::cs)

/-- Contracting a terminal 1 after a positive prefix yields a normalized tail. -/
theorem contracted_normalized (pre : List ℤ) (b : ℤ)
    (hp : ∀ c ∈ pre, 1 ≤ c) (hb : 1 ≤ b) : Normalized (pre ++ [b+1]) := by
  induction pre with
  | nil => simp only [List.nil_append, Normalized]; omega
  | cons c cs ih =>
    have hc := hp c (by simp)
    have ht := ih (fun d hd => hp d (by simp [hd]))
    cases cs with
    | nil => simpa [Normalized] using And.intro hc ht
    | cons d ds => exact ⟨hc, ht⟩

/-- Every normalized nonempty tail has decoded value strictly above 1. -/
theorem normalized_tail_gt_one (b : ℤ) (bs : List ℤ)
    (hn : Normalized (b::bs)) : 1 < finiteValue b (bs.map (fun z : ℤ => (z:ℚ))) := by
  induction bs generalizing b with
  | nil =>
    rw [List.map_nil, finiteValue_nil]
    change 2 ≤ b at hn
    have hb : (2:ℚ) ≤ b := by exact_mod_cast hn
    linarith
  | cons c cs ih =>
    have hc := ih c hn.2
    rw [List.map_cons, finiteValue_cons]
    have hb : (1:ℚ) ≤ b := by exact_mod_cast hn.1
    have hp : 0 < 1 / finiteValue c (cs.map (fun z : ℤ => (z:ℚ))) :=
      one_div_pos.mpr (lt_trans (by norm_num) hc)
    linarith

/-- Positive partial quotients keep every decoded tail denominator nonzero,
including the noncanonical terminal-1 case. Apply recursively to each suffix. -/
theorem positive_tail_value (b : ℤ) (bs : List ℤ) (hb : 1 ≤ b)
    (hs : ∀ c ∈ bs, 1 ≤ c) : 1 ≤ finiteValue b (bs.map (fun z : ℤ => (z:ℚ))) := by
  induction bs generalizing b with
  | nil => simpa [finiteValue_nil] using (show (1:ℚ) ≤ b by exact_mod_cast hb)
  | cons c cs ih =>
    have hc := ih c (hs c (by simp)) (fun d hd => hs d (by simp [hd]))
    rw [List.map_cons, finiteValue_cons]
    have hbc : (1:ℚ) ≤ b := by exact_mod_cast hb
    have hp : 0 < 1 / finiteValue c (cs.map (fun z : ℤ => (z:ℚ))) :=
      one_div_pos.mpr (by linarith)
    linarith

/-- Decode and reconstruct any normalized finite integral simple presentation.
This is equality of the actual head and whole coefficient sequence. -/
theorem reconstruct_normalized (a : ℤ) (bs : List ℤ) (hn : Normalized bs) :
    GenContFract.of (finiteValue a (bs.map (fun z : ℤ => (z:ℚ)))) =
      finitePresentation a (bs.map (fun z : ℤ => (z:ℚ))) := by
  induction bs generalizing a with
  | nil =>
    simp only [List.map_nil, finiteValue_nil]
    apply GenContFract.ext
    · simp [GenContFract.of_h_eq_floor, finitePresentation]
    · simp [GenContFract.of_s_of_int, finitePresentation, Stream'.Seq.ofList_nil]
  | cons b bs ih =>
    have htail : Normalized bs := by cases bs <;> simp_all [Normalized]
    have hi := ih b htail
    let v := finiteValue b (bs.map (fun z : ℤ => (z:ℚ)))
    have hv : 1 < v := normalized_tail_gt_one b bs hn
    have hp : 0 < 1/v := one_div_pos.mpr (by linarith)
    have hl : 1/v < 1 := (div_lt_one (by linarith : 0<v)).mpr hv
    have hfloor : ⌊(a:ℚ)+1/v⌋ = a := Int.floor_eq_iff.mpr ⟨by linarith,by linarith⟩
    have hfract : Int.fract ((a:ℚ)+1/v) = 1/v := by
      rw [Int.fract, hfloor]; ring
    have hinv : (Int.fract ((a:ℚ)+1/v))⁻¹ = v := by rw [hfract, one_div, inv_inv]
    have hne : Int.fract ((a:ℚ)+1/v) ≠ 0 := by rw [hfract]; exact ne_of_gt hp
    have hb : (⌊v⌋ : ℚ) = b := by
      have hh := congrArg GenContFract.h hi
      simpa [GenContFract.of_h_eq_floor, finitePresentation, v] using hh
    simp only [List.map_cons, finiteValue_cons]
    change GenContFract.of ((a:ℚ)+1/v) = finitePresentation a ((b:ℚ)::bs.map (fun z : ℤ => (z:ℚ)))
    apply GenContFract.ext
    · change (GenContFract.of ((a:ℚ)+1/v)).h = (a:ℚ)
      rw [GenContFract.of_h_eq_floor, hfloor]
    · apply Stream'.Seq.ext
      intro n
      cases n with
      | zero =>
        change (GenContFract.of ((a:ℚ)+1/v)).s.head = _
        rw [GenContFract.of_s_head hne, hinv, hb]
        simp [finitePresentation,Stream'.Seq.ofList_cons]
      | succ n =>
        rw [GenContFract.of_s_succ, hinv]
        rw [hi]
        simp [finitePresentation,Stream'.Seq.ofList_cons]

theorem integral_presentation_injective {a b : ℤ} {xs ys : List ℤ}
    (h : finitePresentation a (xs.map (fun z : ℤ => (z:ℚ))) =
      finitePresentation b (ys.map (fun z : ℤ => (z:ℚ)))) : a=b ∧ xs=ys := by
  constructor
  · have hh := congrArg GenContFract.h h
    change (a:ℚ) = b at hh
    exact_mod_cast hh
  · have hs := congrArg GenContFract.s h
    have hm : xs.map (fun z : ℤ => (⟨1,(z:ℚ)⟩ : GenContFract.Pair ℚ)) =
        ys.map (fun z : ℤ => (⟨1,(z:ℚ)⟩ : GenContFract.Pair ℚ)) := by
      simpa only [finitePresentation, List.map_map, Function.comp_def] using
        Stream'.Seq.ofList_injective hs
    exact (List.map_inj_right (fun u v huv => by
      have hb := congrArg GenContFract.Pair.b huv
      change (u:ℚ) = v at hb
      exact_mod_cast hb)).mp hm

/-- Full finite uniqueness for the stated normalized integral tail convention.
No claim about infinite presentations. -/
theorem normalized_unique (a b : ℤ) (xs ys : List ℤ)
    (hx : Normalized xs) (hy : Normalized ys) :
    finiteValue a (xs.map (fun z : ℤ => (z:ℚ))) =
      finiteValue b (ys.map (fun z : ℤ => (z:ℚ))) ↔ a=b ∧ xs=ys := by
  constructor
  · intro hv
    apply integral_presentation_injective
    rw [← reconstruct_normalized a xs hx, ← reconstruct_normalized b ys hy, hv]
  · rintro ⟨rfl,rfl⟩; rfl

open Filter
open scoped Topology

/-- Direct reuse of pinned mathlib's canonical-expansion convergence. -/
theorem canonical_converges (x : ℝ) :
    Tendsto (GenContFract.of x).convs atTop (𝓝 x) := GenContFract.of_convergence x

theorem canonical_accuracy (x ε : ℝ) (he : 0<ε) :
    ∃ N : ℕ, ∀ n ≥ N, |x - (GenContFract.of x).convs n| < ε :=
  GenContFract.of_convergence_epsilon x ε he

/-- Canonical expansion uniquely determines any real input, including irrationals.
This does not quantify over arbitrary infinite coefficient streams. -/
theorem canonical_injective (x y : ℝ) :
    GenContFract.of x = GenContFract.of y ↔ x=y := by
  constructor
  · intro h
    have hy := canonical_converges y
    rw [← h] at hy
    exact tendsto_nhds_unique (canonical_converges x) hy
  · rintro rfl; rfl

theorem irrational_infinite (x : ℝ) (hx : ¬ ∃ q : ℚ, x=(q:ℝ)) :
    ¬ (GenContFract.of x).Terminates := fun ht => hx ((finite_iff_rational x).mp ht)

theorem irrational_entry_present (x : ℝ) (hx : ¬ ∃ q : ℚ, x=(q:ℝ)) (n : ℕ) :
    (GenContFract.of x).s.get? n ≠ none :=
  fun hn => irrational_infinite x hx ⟨n,hn⟩

theorem irrational_no_exact_truncation (x : ℝ)
    (hx : ¬ ∃ q : ℚ, x=(q:ℝ)) (n : ℕ) : (GenContFract.of x).convs n ≠ x := by
  obtain ⟨q,hq⟩ := GenContFract.exists_rat_eq_nth_conv x n
  intro he
  exact hx ⟨q,he.symm.trans hq⟩

/-- Exact rational witness for each finite convergent. This choice-based
conversion is mathematical, not an executable real-input algorithm. -/
noncomputable def rationalConvergent (x : ℝ) (n : ℕ) : ℚ :=
  Classical.choose (GenContFract.exists_rat_eq_nth_conv x n)

theorem rationalConvergent_cast (x : ℝ) (n : ℕ) :
    (rationalConvergent x n : ℝ) = (GenContFract.of x).convs n :=
  (Classical.choose_spec (GenContFract.exists_rat_eq_nth_conv x n)).symm

/-- Concrete correspondence from canonical fractions to the existing §2.15.2
rational-stream interpretation, preserving the exact represented real. -/
theorem rational_stream_represents (x : ℝ) :
    SequenceRepresentations.Represents (rationalConvergent x) x := by
  simpa only [SequenceRepresentations.Represents,rationalConvergent_cast] using canonical_converges x

theorem rational_stream_unique (x y : ℝ)
    (hy : SequenceRepresentations.Represents (rationalConvergent x) y) : x=y :=
  SequenceRepresentations.unique (rational_stream_represents x) hy

/-- Rational inputs become exactly constant eventually under the same conversion. -/
theorem rational_stream_eventually_exact (q : ℚ) :
    ∀ᶠ n in atTop, rationalConvergent (q:ℝ) n = q := by
  have h := GenContFract.of_correctness_atTop_of_terminates
    ((finite_iff_rational (q:ℝ)).mpr ⟨q,rfl⟩)
  filter_upwards [h] with n hn
  apply Rat.cast_injective (α := ℝ)
  rw [rationalConvergent_cast]
  exact hn.symm

end GeneralizedIntervalArithmetic.ContinuedFractionConversion
