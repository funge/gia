import ContinuedFractionConversion

/-! The arbitrary infinite simple-stream converse. Suffix convergence is proved
from admissibility by two-step contraction, then used for canonical recovery. -/
namespace GeneralizedIntervalArithmetic.InfiniteSimpleCF
open Filter
open scoped Topology

/-- Source simple coefficients: nonnegative integral head, positive integral tails.
There is no last coefficient in this genuinely infinite presentation. -/
def Admissible (a : ℕ→ℤ) : Prop := 0≤a 0 ∧ ∀n, 1≤a (n+1)

/-- Rational finite observation of the suffix starting at n, with k further terms. -/
def trunc (a : ℕ→ℤ) (n : ℕ) : ℕ→ℚ
  | 0 => a n
  | k+1 => (a n:ℚ) + 1 / trunc a (n+1) k

/-- Bridge to the existing finite evaluator, not a new decoding convention. -/
theorem trunc_finite (a : ℕ→ℤ) (n k : ℕ) :
    trunc a n k = ContinuedFractionConversion.finiteValue (a n)
      ((List.range k).map (fun j => (a (n+j+1):ℚ))) := by
  induction k generalizing n with
  | zero => simp [trunc,ContinuedFractionConversion.finiteValue_nil]
  | succ k ih =>
    rw [List.range_succ_eq_map,List.map_cons,ContinuedFractionConversion.finiteValue_cons]
    simp only [trunc,ih,List.map_map,Function.comp_def,Nat.add_zero]
    congr 3
    apply List.map_congr_left
    intro j _
    congr 2; omega

/-- Actual mathlib generalized fraction, with all partial numerators one. -/
def presentation (a : ℕ→ℤ) : GenContFract ℝ :=
  ⟨a 0,Stream'.Seq.ofStream (fun n => ⟨1,(a (n+1):ℝ)⟩)⟩

def SuffixLimits (a : ℕ→ℤ) (v : ℕ→ℝ) : Prop :=
  ∀n, Tendsto (fun k => (trunc a n k:ℝ)) atTop (𝓝 (v n))

theorem trunc_bounds {a : ℕ→ℤ} (ha : Admissible a) (n k : ℕ) :
    (a n:ℚ) ≤ trunc a n k ∧ trunc a n k ≤ (a n:ℚ)+1 := by
  induction k generalizing n with
  | zero => simp [trunc]
  | succ k ih =>
    have h := ih (n+1)
    have hp : (1:ℚ) ≤ trunc a (n+1) k :=
      (show (1:ℚ)≤a (n+1) by exact_mod_cast ha.2 n).trans h.1
    have hi : 0 < (1:ℚ)/trunc a (n+1) k := one_div_pos.mpr (by linarith)
    have hu : (1:ℚ)/trunc a (n+1) k ≤ 1 := (div_le_one (by linarith)).mpr hp
    simp only [trunc]
    constructor <;> linarith

theorem limits_bounds {a : ℕ→ℤ} {v : ℕ→ℝ} (ha : Admissible a)
    (hv : SuffixLimits a v) (n : ℕ) : (a n:ℝ)≤v n ∧ v n≤(a n:ℝ)+1 := by
  constructor
  · exact ge_of_tendsto (hv n) (Filter.Eventually.of_forall (fun k => by exact_mod_cast (trunc_bounds ha n k).1))
  · exact le_of_tendsto (hv n) (Filter.Eventually.of_forall (fun k => by exact_mod_cast (trunc_bounds ha n k).2))

theorem limits_recurrence {a : ℕ→ℤ} {v : ℕ→ℝ} (ha : Admissible a)
    (hv : SuffixLimits a v) (n : ℕ) : v n = (a n:ℝ) + 1/v (n+1) := by
  have hp : (1:ℝ)≤v (n+1) :=
    (show (1:ℝ)≤a (n+1) by exact_mod_cast ha.2 n).trans (limits_bounds ha hv (n+1)).1
  have hr := (tendsto_const_nhds (x:=(a n:ℝ))).add ((tendsto_const_nhds (x:=(1:ℝ))).div (hv (n+1)) (by linarith : v (n+1)≠0))
  have hs := (hv n).comp (tendsto_add_atTop_nat 1)
  apply tendsto_nhds_unique hs
  convert hr using 1
  funext k
  simp [trunc]

/-- A complete-quotient witness makes floor recovery valid, rather than merely
postulating a limit of whole fractions. -/
def Quotients (a : ℕ→ℤ) (v : ℕ→ℝ) : Prop :=
  (∀n, (a n:ℝ)<v n ∧ v n<(a n:ℝ)+1) ∧
  ∀n, v n=(a n:ℝ)+1/v (n+1)

theorem limits_quotients {a : ℕ→ℤ} {v : ℕ→ℝ} (ha : Admissible a)
    (hv : SuffixLimits a v) : Quotients a v := by
  have hp (n : ℕ) : (0:ℝ)<v (n+1) := by
    have h := (limits_bounds ha hv (n+1)).1
    have h' : (1:ℝ)≤a (n+1) := by exact_mod_cast ha.2 n
    linarith
  have hlo (n : ℕ) : (a n:ℝ)<v n := by
    rw [limits_recurrence ha hv n]
    exact lt_add_of_pos_right _ (one_div_pos.mpr (hp n))
  refine ⟨?_,limits_recurrence ha hv⟩
  intro n
  refine ⟨hlo n,?_⟩
  have hn := hlo (n+1)
  have h' : (1:ℝ)≤a (n+1) := by exact_mod_cast ha.2 n
  have hi : (1:ℝ)/v (n+1)<1 := (div_lt_one (hp n)).mpr (by linarith)
  rw [limits_recurrence ha hv n]
  linarith

theorem quotient_floor {a : ℕ→ℤ} {v : ℕ→ℝ} (h : Quotients a v) (n : ℕ) :
    ⌊v n⌋ = a n := Int.floor_eq_iff.mpr ⟨(h.1 n).1.le,(h.1 n).2⟩

theorem quotient_step {a : ℕ→ℤ} {v : ℕ→ℝ} (h : Quotients a v) (n : ℕ) :
    Int.fract (v n) ≠ 0 ∧ (Int.fract (v n))⁻¹=v (n+1) := by
  have hf : Int.fract (v n)=1/v (n+1) := by
    rw [Int.fract,quotient_floor h n,h.2 n]; ring
  have hn : Int.fract (v n)>0 := by
    rw [Int.fract,quotient_floor h n]
    linarith [(h.1 n).1]
  exact ⟨ne_of_gt hn,by rw [hf,one_div,inv_inv]⟩

theorem quotient_coefficients {a : ℕ→ℤ} {v : ℕ→ℝ} (h : Quotients a v) (n k : ℕ) :
    (GenContFract.of (v n)).s.get? k = some ⟨1,(a (n+k+1):ℝ)⟩ := by
  induction k generalizing n with
  | zero =>
    change (GenContFract.of (v n)).s.head = _
    rw [GenContFract.of_s_head (quotient_step h n).1,(quotient_step h n).2,quotient_floor h (n+1)]
  | succ k ih =>
    rw [GenContFract.of_s_succ,(quotient_step h n).2,ih]
    congr 4; omega

theorem reconstruct {a : ℕ→ℤ} {v : ℕ→ℝ} (h : Quotients a v) :
    GenContFract.of (v 0) = presentation a := by
  apply GenContFract.ext
  · simp [GenContFract.of_h_eq_floor,quotient_floor h,presentation]
  · apply Stream'.Seq.ext
    intro k
    rw [quotient_coefficients h]
    change (some ⟨(1:ℝ),(a (0+k+1):ℝ)⟩ : Option (GenContFract.Pair ℝ)) = some ⟨1,(a (k+1):ℝ)⟩
    simp

theorem presentation_infinite (a : ℕ→ℤ) : ¬ (presentation a).Terminates := by
  rintro ⟨n,hn⟩
  change (some ⟨(1:ℝ),(a (n+1):ℝ)⟩ : Option (GenContFract.Pair ℝ)) = none at hn
  contradiction

theorem irrational {a : ℕ→ℤ} {v : ℕ→ℝ} (h : Quotients a v) :
    ¬∃q:ℚ, v 0=(q:ℝ) := by
  intro hr
  have ht := (ContinuedFractionConversion.finite_iff_rational (v 0)).2 hr
  rw [reconstruct h] at ht
  exact presentation_infinite a ht

theorem converges {a : ℕ→ℤ} {v : ℕ→ℝ} (h : Quotients a v) :
    Tendsto (presentation a).convs atTop (𝓝 (v 0)) := by
  rw [←reconstruct h]
  exact ContinuedFractionConversion.canonical_converges _

theorem quotient_unique {a : ℕ→ℤ} {v w : ℕ→ℝ}
    (hv : Quotients a v) (hw : Quotients a w) : v 0=w 0 :=
  tendsto_nhds_unique (converges hv) (converges hw)

/-- Conditional intermediate converse; suffix_limits_exist below discharges its premise. -/
theorem suffix_converse {a : ℕ→ℤ} {v : ℕ→ℝ} (ha : Admissible a)
    (hv : SuffixLimits a v) :
    GenContFract.of (v 0)=presentation a ∧ (¬∃q:ℚ,v 0=(q:ℝ)) ∧
      Tendsto (presentation a).convs atTop (𝓝 (v 0)) :=
  ⟨reconstruct (limits_quotients ha hv),irrational (limits_quotients ha hv),
    converges (limits_quotients ha hv)⟩



/-- Finite fractional tail, used to prove convergence rather than assume it. -/
noncomputable def fraction (a : ℕ→ℤ) (n : ℕ) : ℕ→ℝ
  | 0 => 0
  | k+1 => 1 / ((a (n+1):ℝ)+fraction a (n+1) k)

theorem fraction_range {a : ℕ→ℤ} (ha : Admissible a) (n k : ℕ) :
    fraction a n k ∈ Set.Icc 0 1 := by
  induction k generalizing n with
  | zero => simp [fraction]
  | succ k ih =>
    have hr := ih (n+1)
    have hb : (1:ℝ)≤a (n+1) := by exact_mod_cast ha.2 n
    have hp : 0<(a (n+1):ℝ)+fraction a (n+1) k := by linarith [hr.1]
    exact ⟨(one_div_pos.mpr hp).le,(div_le_one hp).mpr (by linarith [hr.1])⟩

theorem trunc_fraction (a : ℕ→ℤ) (n k : ℕ) :
    (trunc a n k:ℝ)=(a n:ℝ)+fraction a n k := by
  induction k generalizing n with
  | zero => simp [trunc,fraction]
  | succ k ih => simp [trunc,fraction,ih]

/-- Two positive simple steps contract tail differences by at least four.
One step alone need not have a strict uniform contraction. -/
theorem two_step {b c x y : ℝ} (hb : 1≤b) (hc : 1≤c)
    (hx : x∈Set.Icc 0 1) (hy : y∈Set.Icc 0 1) :
    |1/(b+1/(c+x))-1/(b+1/(c+y))| ≤ |x-y|/4 := by
  have hcx : 0<c+x := by linarith [hx.1]
  have hcy : 0<c+y := by linarith [hy.1]
  have hbx : 0<b+1/(c+x) := by have := one_div_pos.mpr hcx; linarith
  have hby : 0<b+1/(c+y) := by have := one_div_pos.mpr hcy; linarith
  have hdx : 2≤b*(c+x)+1 := by
    have hp := mul_le_mul hb (show 1≤c+x by linarith [hx.1]) (by norm_num : (0:ℝ)≤1) (by linarith : 0≤b)
    nlinarith
  have hdy : 2≤b*(c+y)+1 := by
    have hp := mul_le_mul hb (show 1≤c+y by linarith [hy.1]) (by norm_num : (0:ℝ)≤1) (by linarith : 0≤b)
    nlinarith
  have hden : 4≤(b*(c+x)+1)*(b*(c+y)+1) := by nlinarith
  have he : 1/(b+1/(c+x))-1/(b+1/(c+y)) =
      (x-y)/((b*(c+x)+1)*(b*(c+y)+1)) := by
    field_simp
    ring
  rw [he,abs_div,abs_of_pos (by linarith : 0<(b*(c+x)+1)*(b*(c+y)+1))]
  apply (div_le_iff₀ (by linarith : 0<(b*(c+x)+1)*(b*(c+y)+1))).mpr
  nlinarith [abs_nonneg (x-y)]

theorem fraction_gap {a : ℕ→ℤ} (ha : Admissible a) (N n m : ℕ) :
    |fraction a n (2*N+m)-fraction a n (2*N)| ≤ (1/4:ℝ)^N := by
  induction N generalizing n with
  | zero =>
    have h := fraction_range ha n m
    simpa [fraction,abs_of_nonneg h.1] using h.2
  | succ N ih =>
    have h1 : 2*(N+1)+m=(2*N+m)+1+1 := by omega
    have h2 : 2*(N+1)=(2*N)+1+1 := by omega
    rw [h1,h2]
    simp only [fraction]
    have hs := two_step (b:=(a (n+1):ℝ)) (c:=(a (n+1+1):ℝ))
      (by exact_mod_cast ha.2 n) (by exact_mod_cast ha.2 (n+1))
      (fraction_range ha (n+1+1) (2*N+m)) (fraction_range ha (n+1+1) (2*N))
    apply hs.trans
    have hi := ih (n+1+1)
    rw [pow_succ]
    nlinarith

theorem fraction_cauchy {a : ℕ→ℤ} (ha : Admissible a) (n : ℕ) :
    CauchySeq (fraction a n) := by
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1)
  obtain ⟨N,hN⟩ := (hg.eventually (gt_mem_nhds hε)).exists
  refine ⟨2*N,?_⟩
  intro k hk
  have hh := fraction_gap ha N n (k-2*N)
  rw [Nat.add_sub_of_le hk] at hh
  have hd : dist (fraction a n k) (fraction a n (2*N)) ≤ (1/4:ℝ)^N := by
    simpa [Real.dist_eq] using hh
  exact hd.trans_lt hN

/-- Existence for every admissible stream, discharged by two-step contraction. -/
theorem suffix_limits_exist {a : ℕ→ℤ} (ha : Admissible a) : ∃v, SuffixLimits a v := by
  have he (n : ℕ) : ∃x:ℝ, Tendsto (fraction a n) atTop (𝓝 x) :=
    cauchySeq_tendsto_of_complete (fraction_cauchy ha n)
  choose w hw using he
  refine ⟨fun n => (a n:ℝ)+w n,?_⟩
  intro n
  simpa only [trunc_fraction] using (tendsto_const_nhds (x:=(a n:ℝ))).add (hw n)

/-- Full arbitrary admissible infinite simple-stream converse. -/
theorem admissible_reconstruction {a : ℕ→ℤ} (ha : Admissible a) :
    ∃x:ℝ, (0<x) ∧ (¬∃q:ℚ,x=(q:ℝ)) ∧ GenContFract.of x=presentation a ∧
      Tendsto (presentation a).convs atTop (𝓝 x) := by
  obtain ⟨v,hv⟩ := suffix_limits_exist ha
  have hq := limits_quotients ha hv
  have hp : (0:ℝ)<v 0 := by
    have hz : (0:ℝ)≤a 0 := by exact_mod_cast ha.1
    linarith [(hq.1 0).1]
  exact ⟨v 0,hp,irrational hq,reconstruct hq,converges hq⟩



theorem presentation_injective {a b : ℕ→ℤ} (h : presentation a=presentation b) : a=b := by
  funext n
  cases n with
  | zero =>
    have hh := congrArg GenContFract.h h
    change (a 0:ℝ)=(b 0:ℝ) at hh
    exact_mod_cast hh
  | succ n =>
    have hs := congrArg (fun g : GenContFract ℝ => g.s.get? n) h
    change some (⟨1,(a (n+1):ℝ)⟩ : GenContFract.Pair ℝ) = some ⟨1,(b (n+1):ℝ)⟩ at hs
    have hh := congrArg GenContFract.Pair.b (Option.some.inj hs)
    change (a (n+1):ℝ)=(b (n+1):ℝ) at hh
    exact_mod_cast hh

def Represents (a : ℕ→ℤ) (x : ℝ) : Prop :=
  Tendsto (presentation a).convs atTop (𝓝 x)

/-- Convergence, with admissibility, gives exact canonical recovery. -/
theorem represents_iff {a : ℕ→ℤ} (ha : Admissible a) (x : ℝ) :
    Represents a x ↔ GenContFract.of x=presentation a := by
  constructor
  · intro hx
    obtain ⟨y,_,_,hy,hlim⟩ := admissible_reconstruction ha
    have he : x=y := tendsto_nhds_unique hx hlim
    simpa [he] using hy
  · intro h
    unfold Represents
    rw [←h]
    exact ContinuedFractionConversion.canonical_converges x

theorem unique_value {a : ℕ→ℤ} (ha : Admissible a) : ∃!x:ℝ, Represents a x := by
  obtain ⟨x,_,_,_,hx⟩ := admissible_reconstruction ha
  exact ⟨x,hx,fun y hy => tendsto_nhds_unique hy hx⟩

/-- Source equality of values iff equality of all coefficients, for this class. -/
theorem representation_unique {a b : ℕ→ℤ} {x y : ℝ}
    (ha : Admissible a) (hb : Admissible b) (hx : Represents a x) (hy : Represents b y) :
    x=y ↔ a=b := by
  constructor
  · intro hxy
    apply presentation_injective
    rw [←(represents_iff ha x).1 hx,←(represents_iff hb y).1 hy,hxy]
  · rintro rfl
    exact tendsto_nhds_unique hx hy

theorem represented_irrational {a : ℕ→ℤ} {x : ℝ} (ha : Admissible a) (hx : Represents a x) :
    ¬∃q:ℚ,x=(q:ℝ) := by
  obtain ⟨y,_,hy,_,hlim⟩ := admissible_reconstruction ha
  have he : x=y := tendsto_nhds_unique hx hlim
  simpa [he] using hy



/-- Derived uniform accuracy for finite truncations, not a source-asserted rate
or a claim that arbitrary supplied coefficient streams are computable. -/
theorem limit_error {a : ℕ→ℤ} {v : ℕ→ℝ} (ha : Admissible a)
    (hv : SuffixLimits a v) (n N : ℕ) :
    |v n-(trunc a n (2*N):ℝ)| ≤ (1/4:ℝ)^N := by
  have hs := (hv n).comp (tendsto_add_atTop_nat (2*N))
  have hl := (hs.sub_const (trunc a n (2*N):ℝ)).abs
  apply le_of_tendsto hl
  apply Filter.Eventually.of_forall
  intro m
  have hh := fraction_gap ha N n m
  simpa only [Function.comp_apply,trunc_fraction,Nat.add_comm m (2*N),add_sub_add_left_eq_sub] using hh

end GeneralizedIntervalArithmetic.InfiniteSimpleCF
