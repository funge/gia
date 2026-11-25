import InfiniteSimpleCF

/-! Signed infinite simple fractions under the printed §2.15.7 restrictions.
No extraction algorithm or unique signed presentation is postulated. -/
namespace GeneralizedIntervalArithmetic.RedundantCF
open Filter
open scoped Topology

/-- Infinite case of the printed restrictions. The integral head is unrestricted. -/
def Admissible (a : ℕ → ℤ) : Prop :=
  (∀ n, 2 ≤ |a (n+1)|) ∧
  (∀ n, |a (n+1)| = 2 → 0 < a (n+1) * a (n+2))

/-- Reuse the existing simple-fraction observation, allowing signed coefficients. -/
noncomputable abbrev fraction := InfiniteSimpleCF.fraction
abbrev trunc := InfiniteSimpleCF.trunc

/-- Fractional suffixes stay in the half-unit interval and retain the sign of
 their first coefficient. This invariant uses the adjacent-sign restriction. -/
theorem fraction_invariant {a : ℕ → ℤ} (ha : Admissible a) (n k : ℕ) :
    |fraction a n k| ≤ 1/2 ∧ 0 ≤ (a (n+1):ℝ) * fraction a n k := by
  induction k generalizing n with
  | zero => simp [InfiniteSimpleCF.fraction]
  | succ k ih =>
    have ht := ih (n+1)
    have hb : (2:ℝ) ≤ |(a (n+1):ℝ)| := by exact_mod_cast ha.1 n
    have hx := abs_le.mp ht.1
    have hd : (2:ℝ) ≤ |(a (n+1):ℝ) + fraction a (n+1) k| := by
      by_cases he : |a (n+1)| = 2
      · have he' : |(a (n+1):ℝ)| = 2 := by exact_mod_cast he
        have hs : (0:ℝ) < (a (n+1):ℝ) * (a (n+2):ℝ) := by exact_mod_cast ha.2 n he
        have hi := ht.2
        have hn : n+1+1=n+2 := by omega
        rw [hn] at hi
        rcases le_total 0 (a (n+1):ℝ) with hp | hp
        · rw [abs_of_nonneg hp] at he'
          have hy : 0 ≤ fraction a (n+1) k := by nlinarith
          rw [abs_of_nonneg (by linarith)]
          linarith
        · rw [abs_of_nonpos hp] at he'
          have hy : fraction a (n+1) k ≤ 0 := by nlinarith
          rw [abs_of_nonpos (by linarith)]
          linarith
      · have hb3 : (3:ℝ) ≤ |(a (n+1):ℝ)| := by
          have : 3 ≤ |a (n+1)| := by have := ha.1 n; omega
          exact_mod_cast this
        have hh := abs_add ( (a (n+1):ℝ) + fraction a (n+1) k) (-fraction a (n+1) k)
        simp only [add_neg_cancel_right,abs_neg] at hh
        linarith
    have hd0 : (a (n+1):ℝ) + fraction a (n+1) k ≠ 0 := by
      intro h; rw [h,abs_zero] at hd; norm_num at hd
    constructor
    · simp only [InfiniteSimpleCF.fraction,abs_div,abs_one]
      exact (div_le_iff₀ (by linarith : 0 < |(a (n+1):ℝ)+fraction a (n+1) k|)).mpr (by linarith)
    · simp only [InfiniteSimpleCF.fraction]
      rcases le_total 0 (a (n+1):ℝ) with hp | hp
      · rw [abs_of_nonneg hp] at hb
        exact mul_nonneg hp (one_div_nonneg.mpr (by linarith))
      · rw [abs_of_nonpos hp] at hb
        exact mul_nonneg_of_nonpos_of_nonpos hp (one_div_nonpos.mpr (by linarith))

/-- A single step is uniformly contractive on these fractional observations. -/
theorem step_contract {b x y : ℝ} (hb : 2 ≤ |b|)
    (hx : |x| ≤ 1/2) (hy : |y| ≤ 1/2) :
    |1/(b+x)-1/(b+y)| ≤ (4/9:ℝ)* |x-y| := by
  have hdx : 3/2 ≤ |b+x| := by
    have h := abs_add (b+x) (-x)
    simp only [add_neg_cancel_right,abs_neg] at h
    linarith
  have hdy : 3/2 ≤ |b+y| := by
    have h := abs_add (b+y) (-y)
    simp only [add_neg_cancel_right,abs_neg] at h
    linarith
  have hnx : b+x ≠ 0 := by intro h; rw [h,abs_zero] at hdx; linarith
  have hny : b+y ≠ 0 := by intro h; rw [h,abs_zero] at hdy; linarith
  have he : 1/(b+x)-1/(b+y) = (y-x)/((b+x)*(b+y)) := by field_simp
  rw [he,abs_div,abs_mul,abs_sub_comm y x]
  have hp : 9/4 ≤ |b+x| * |b+y| := by nlinarith
  apply (div_le_iff₀ (by nlinarith : 0 < |b+x| * |b+y|)).mpr
  nlinarith [abs_nonneg (x-y)]

theorem fraction_gap {a : ℕ → ℤ} (ha : Admissible a) (N n m : ℕ) :
    |fraction a n (N+m)-fraction a n N| ≤ (4/9:ℝ)^N := by
  induction N generalizing n with
  | zero =>
    have h := (fraction_invariant ha n m).1
    simpa [InfiniteSimpleCF.fraction] using h.trans (by norm_num : (1/2:ℝ)≤1)
  | succ N ih =>
    rw [show N+1+m=(N+m)+1 by omega]
    simp only [fraction,InfiniteSimpleCF.fraction]
    have hs := step_contract (b:=(a (n+1):ℝ))
      (by exact_mod_cast ha.1 n)
      (fraction_invariant ha (n+1) (N+m)).1 (fraction_invariant ha (n+1) N).1
    apply hs.trans
    have hi := ih (n+1)
    rw [pow_succ]
    nlinarith

theorem fraction_cauchy {a : ℕ → ℤ} (ha : Admissible a) (n : ℕ) :
    CauchySeq (fraction a n) := by
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤4/9) (by norm_num : (4/9:ℝ)<1)
  obtain ⟨N,hN⟩ := (hg.eventually (gt_mem_nhds hε)).exists
  refine ⟨N,?_⟩
  intro k hk
  have hh := fraction_gap ha N n (k-N)
  rw [Nat.add_sub_of_le hk] at hh
  exact (show dist (fraction a n k) (fraction a n N) ≤ (4/9:ℝ)^N by simpa [Real.dist_eq] using hh).trans_lt hN

/-- Existence follows for the full printed infinite admissible class, including
sign changes. It is not assumed as a suffix-limit premise. -/
theorem suffix_limits_exist {a : ℕ → ℤ} (ha : Admissible a) :
    ∃ v, InfiniteSimpleCF.SuffixLimits a v := by
  have he (n : ℕ) : ∃ x:ℝ, Tendsto (fraction a n) atTop (𝓝 x) :=
    cauchySeq_tendsto_of_complete (fraction_cauchy ha n)
  choose w hw using he
  refine ⟨fun n => (a n:ℝ)+w n,?_⟩
  intro n
  simpa only [InfiniteSimpleCF.trunc_fraction] using (tendsto_const_nhds (x:=(a n:ℝ))).add (hw n)

def Represents (a : ℕ → ℤ) (x : ℝ) : Prop :=
  Tendsto (fun k => (trunc a 0 k:ℝ)) atTop (𝓝 x)

theorem unique_value {a : ℕ → ℤ} (ha : Admissible a) : ∃! x, Represents a x := by
  obtain ⟨v,hv⟩ := suffix_limits_exist ha
  exact ⟨v 0,hv 0,fun y hy => tendsto_nhds_unique hy (hv 0)⟩

/-- All actual finite observed divisors are separated from zero. -/
theorem trunc_tail_nonzero {a : ℕ → ℤ} (ha : Admissible a) (n k : ℕ) :
    trunc a (n+1) k ≠ 0 := by
  have hb : (2:ℝ) ≤ |(a (n+1):ℝ)| := by exact_mod_cast ha.1 n
  have ht := (fraction_invariant ha (n+1) k).1
  intro hz
  have he := InfiniteSimpleCF.trunc_fraction a (n+1) k
  change InfiniteSimpleCF.trunc a (n+1) k = 0 at hz
  rw [hz] at he
  simp only [Rat.cast_zero] at he
  have he' : (a (n+1):ℝ) = -fraction a (n+1) k := by linarith
  rw [he',abs_neg] at hb
  linarith

theorem limits_bounds {a : ℕ → ℤ} {v : ℕ → ℝ} (ha : Admissible a)
    (hv : InfiniteSimpleCF.SuffixLimits a v) (n : ℕ) :
    |v n-(a n:ℝ)| ≤ 1/2 := by
  apply le_of_tendsto ((hv n).sub_const (a n:ℝ)).abs
  exact Filter.Eventually.of_forall (fun k => by
    simpa only [InfiniteSimpleCF.trunc_fraction,add_sub_cancel_left] using (fraction_invariant ha n k).1)

theorem limits_tail_nonzero {a : ℕ → ℤ} {v : ℕ → ℝ} (ha : Admissible a)
    (hv : InfiniteSimpleCF.SuffixLimits a v) (n : ℕ) : v (n+1) ≠ 0 := by
  have hb : (2:ℝ) ≤ |(a (n+1):ℝ)| := by exact_mod_cast ha.1 n
  have ht := limits_bounds ha hv (n+1)
  intro hz
  rw [hz,zero_sub,abs_neg] at ht
  linarith

/-- Sound recursive real meaning, with nonzero divisors proved separately. -/
theorem limits_recurrence {a : ℕ → ℤ} {v : ℕ → ℝ} (ha : Admissible a)
    (hv : InfiniteSimpleCF.SuffixLimits a v) (n : ℕ) :
    v n = (a n:ℝ)+1/v (n+1) := by
  have hr := (tendsto_const_nhds (x:=(a n:ℝ))).add
    ((tendsto_const_nhds (x:=(1:ℝ))).div (hv (n+1)) (limits_tail_nonzero ha hv n))
  apply tendsto_nhds_unique ((hv n).comp (tendsto_add_atTop_nat 1))
  convert hr using 1
  funext k
  simp [trunc,InfiniteSimpleCF.trunc]

/-- Derived uniform error; no computability of an arbitrary stream is assumed. -/
theorem limit_error {a : ℕ → ℤ} {v : ℕ → ℝ} (ha : Admissible a)
    (hv : InfiniteSimpleCF.SuffixLimits a v) (n N : ℕ) :
    |v n-(trunc a n N:ℝ)| ≤ (4/9:ℝ)^N := by
  have hl := (((hv n).comp (tendsto_add_atTop_nat N)).sub_const (trunc a n N:ℝ)).abs
  apply le_of_tendsto hl
  apply Filter.Eventually.of_forall
  intro m
  simpa only [Function.comp_apply,InfiniteSimpleCF.trunc_fraction,Nat.add_comm m N,add_sub_add_left_eq_sub]
    using fraction_gap ha N n m

/-- Exact finite-prefix interpretation reuses the existing rational decoder. -/
theorem finite_prefix (a : ℕ → ℤ) (n k : ℕ) :
    trunc a n k = ContinuedFractionConversion.finiteValue (a n)
      ((List.range k).map (fun j => (a (n+j+1):ℚ))) :=
  InfiniteSimpleCF.trunc_finite a n k

/-- Signed representation respects negation without changing the coefficient
witness separately at each truncation. -/
theorem trunc_neg (a : ℕ → ℤ) (n k : ℕ) :
    trunc (fun i => -a i) n k = -trunc a n k := by
  induction k generalizing n with
  | zero => simp [trunc,InfiniteSimpleCF.trunc]
  | succ k ih => simp [trunc,InfiniteSimpleCF.trunc,ih,neg_add_rev,add_comm]

theorem admissible_neg {a : ℕ → ℤ} (ha : Admissible a) : Admissible (fun i => -a i) := by
  simpa only [Admissible,abs_neg,neg_mul_neg] using ha

theorem represents_neg {a : ℕ → ℤ} {x : ℝ} (hx : Represents a x) :
    Represents (fun i => -a i) (-x) := by
  simpa only [Represents,trunc_neg,Rat.cast_neg] using hx.neg

/-- On the overlap with the ordinary positive simple convention, the signed
observation has exactly the existing canonical mathlib value. No analogous
identification of negative coefficients with `of` is asserted. -/
theorem positive_recovery {a : ℕ → ℤ} {x : ℝ} (ha : Admissible a)
    (hhead : 0 ≤ a 0) (hpos : ∀ n, 0 < a (n+1)) (hx : Represents a x) :
    GenContFract.of x = InfiniteSimpleCF.presentation a ∧
      (¬∃q:ℚ, x=(q:ℝ)) ∧
      Tendsto (InfiniteSimpleCF.presentation a).convs atTop (𝓝 x) := by
  obtain ⟨v,hv⟩ := suffix_limits_exist ha
  have he : x=v 0 := tendsto_nhds_unique hx (hv 0)
  subst x
  exact InfiniteSimpleCF.suffix_converse ⟨hhead,fun n => by have := hpos n; omega⟩ hv

/-- Literal finite-tail restrictions printed in §2.15.7. These syntax rules
alone do not assert nonzero evaluated suffixes or an extraction algorithm. -/
def FiniteTail : List ℤ → Prop
  | [] => True
  | [b] => b ≠ -2
  | b::c::bs => 2 ≤ |b| ∧ (|b|=2 → 0<b*c) ∧ FiniteTail (c::bs)

end GeneralizedIntervalArithmetic.RedundantCF
