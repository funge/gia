import DigitExtraction
import ExpressionStreams
import ContinuedFractionConversion

/-! Finite observations cannot decide canonical boundary digits of every
nested shrinking rational interval name. The reader sees interval replies only. -/
namespace GeneralizedIntervalArithmetic.FiniteQuery
open Filter
open scoped Topology

abbrev Name := ℕ → QInterval

def Valid (I : Name) (x : ℝ) : Prop :=
  (∀ n, (I n).lo ≤ (I (n+1)).lo ∧ (I (n+1)).hi ≤ (I n).hi) ∧
  (∀ n, (I n).Contains x) ∧ ExpressionStreams.Converges I x

/-- An arbitrary deterministic state machine. The step has no access to the
name except through an explicit indexed request and its interval reply. -/
abbrev Machine (S : Type) := S → Sum ℤ (ℕ × (QInterval → S))

def run {S : Type} (M : Machine S) (I : Name) : ℕ → S → Option ℤ
  | 0, _ => none
  | k+1, s => match M s with
    | .inl z => some z
    | .inr (n,next) => run M I k (next (I n))

def queriedBound {S : Type} (M : Machine S) (I : Name) : ℕ → S → ℕ
  | 0, _ => 0
  | k+1, s => match M s with
    | .inl _ => 0
    | .inr (n,next) => max n (queriedBound M I k (next (I n)))

def queries {S : Type} (M : Machine S) (I : Name) : ℕ → S → List ℕ
  | 0, _ => []
  | k+1, s => match M s with
    | .inl _ => []
    | .inr (n,next) => n :: queries M I k (next (I n))

theorem bound_is_trace_max {S : Type} (M : Machine S) (I : Name) (k : ℕ) (s : S) :
    queriedBound M I k s = (queries M I k s).foldr max 0 := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases he : M s with
    | inl z => simp [queriedBound,queries,he]
    | inr p => rcases p with ⟨n,next⟩; simp [queriedBound,queries,he,ih]

/-- Adaptive, repeated and out-of-order queries are allowed. The bound depends
on the actual run, not on an assumed fixed input prefix or global runtime. -/
theorem run_agrees {S : Type} (M : Machine S) (I J : Name) (k : ℕ) (s : S)
    (h : ∀ n, n ≤ queriedBound M I k s → I n = J n) :
    run M I k s = run M J k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases he : M s with
    | inl z => simp [run,he]
    | inr p =>
      rcases p with ⟨n,next⟩
      have hn : I n=J n := h n (by simp [queriedBound,he])
      simp only [run,he]
      rw [←hn]
      apply ih
      intro j hj
      apply h j
      simpa only [queriedBound,he] using hj.trans (le_max_right n _)

/-- Explicit computable rational radii, uniformly positive and tending to zero. -/
def radius (n : ℕ) : ℚ := (1/2)^(n+5)

theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity

theorem radius_antitone : Antitone radius := by
  apply antitone_nat_of_succ_le
  intro n
  have hp := radius_pos n
  simp only [radius,Nat.succ_add,pow_succ] at *
  linarith

theorem radius_small (n : ℕ) : radius n ≤ 1/32 := by
  simpa [radius] using radius_antitone (Nat.zero_le n)

theorem radius_tends_zero : Tendsto (fun n => (radius n:ℝ)) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  simpa [radius] using h.comp (tendsto_add_atTop_nat 5)

def straddle (q : ℚ) (n : ℕ) : QInterval :=
  ⟨q-radius n,q+radius n,by have := radius_pos n; linarith⟩

theorem straddle_valid (q : ℚ) : Valid (straddle q) q := by
  refine ⟨?_,?_,?_,?_⟩
  · intro n; have := radius_antitone (Nat.le_succ n)
    constructor <;> dsimp [straddle] <;> linarith
  · intro n
    have hp : (0:ℝ) ≤ radius n := by exact_mod_cast (radius_pos n).le
    constructor <;> simp only [straddle,Rat.cast_sub,Rat.cast_add] <;> linarith
  · simpa [straddle] using (tendsto_const_nhds (x:=(q:ℝ))).sub radius_tends_zero
  · simpa [straddle] using (tendsto_const_nhds (x:=(q:ℝ))).add radius_tends_zero

/-- A second computable name agrees through N, then is a constant singleton
strictly below q. The same rational value belongs to every prefix interval. -/
def below (q : ℚ) (N : ℕ) : ℚ := q-radius N/2

def splice (q : ℚ) (N n : ℕ) : QInterval :=
  if n ≤ N then straddle q n else QInterval.point (below q N)

theorem splice_agrees (q : ℚ) (N n : ℕ) (hn : n ≤ N) :
    splice q N n = straddle q n := by simp [splice,hn]

theorem below_in_prefix (q : ℚ) (N n : ℕ) (hn : n ≤ N) :
    q-radius n ≤ below q N ∧ below q N ≤ q+radius n := by
  have hr := radius_antitone hn
  have hp := radius_pos N
  have hp' := radius_pos n
  dsimp [below]
  constructor <;> linarith

theorem splice_valid (q : ℚ) (N : ℕ) : Valid (splice q N) (below q N) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro n
    by_cases hn : n+1 ≤ N
    · have hn' : n ≤ N := by omega
      simp only [splice,hn,hn',↓reduceIte]
      exact (straddle_valid q).1 n
    · by_cases hn' : n ≤ N
      · have hb := below_in_prefix q N n hn'
        simpa [splice,hn,hn',QInterval.point,straddle] using hb
      · simp [splice,hn,hn',QInterval.point]
  · intro n
    by_cases hn : n ≤ N
    · have hb := below_in_prefix q N n hn
      constructor
      · exact_mod_cast (show (splice q N n).lo ≤ below q N by simpa [splice,hn,straddle] using hb.1)
      · exact_mod_cast (show below q N ≤ (splice q N n).hi by simpa [splice,hn,straddle] using hb.2)
    · simp [splice,hn,QInterval.point,QInterval.Contains]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (N+1)] with n hn
    simp [splice,show ¬n≤N by omega,QInterval.point]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (N+1)] with n hn
    simp [splice,show ¬n≤N by omega,QInterval.point]

/-- Concrete constructive adversary for any actual finite run. Both names are
explicit rational programs, not an appeal to an arbitrary uncomputable name. -/
theorem splice_indistinguishable {S : Type} (M : Machine S) (s : S) (q : ℚ) (k : ℕ) :
    let N := queriedBound M (straddle q) k s
    Valid (straddle q) q ∧ Valid (splice q N) (below q N) ∧
      run M (straddle q) k s = run M (splice q N) k s := by
  dsimp only
  refine ⟨straddle_valid q,splice_valid q _,?_⟩
  exact run_agrees M _ _ k s (fun n hn => (splice_agrees q _ n hn).symm)

/-- Every finite answer is wrong either on the explicit boundary name or on
one explicit computable splice. This statement needs no correctness assumption
on arbitrary noncomputable names. -/
theorem boundary_counterexample {S : Type} (M : Machine S) (s : S)
    (target : ℝ → ℤ) (q : ℚ)
    (hdiff : ∀ N, target (q:ℝ) ≠ target (below q N:ℝ))
    (k : ℕ) (z : ℤ) (hr : run M (straddle q) k s = some z) :
    z ≠ target (q:ℝ) ∨ ∃ N, Valid (splice q N) (below q N) ∧
      run M (splice q N) k s = some z ∧ z ≠ target (below q N:ℝ) := by
  by_cases hz : z=target (q:ℝ)
  · let N := queriedBound M (straddle q) k s
    have he := (splice_indistinguishable M s q k).2.2
    refine Or.inr ⟨N,splice_valid q N,he.symm.trans hr,?_⟩
    rw [hz]
    exact hdiff N
  · exact Or.inl hz

/-- Generic boundary obstruction. Correctness on all valid names forces every
finite run on the boundary-straddling name to withhold an answer. -/
theorem boundary_obstruction {S : Type} (M : Machine S) (s : S)
    (target : ℝ → ℤ) (q : ℚ) (D : ℝ → Prop)
    (hq : D q) (hbelow : ∀ N, D (below q N))
    (hdiff : ∀ N, target (q:ℝ) ≠ target (below q N:ℝ))
    (hsound : ∀ I x k z, Valid I x → D x → run M I k s = some z → z=target x) :
    ∀ k, run M (straddle q) k s = none := by
  intro k
  cases hr : run M (straddle q) k s with
  | none => rfl
  | some z =>
    have hfirst := hsound (straddle q) q k z (straddle_valid q) hq hr
    let N := queriedBound M (straddle q) k s
    have he := run_agrees M (straddle q) (splice q N) k s (fun n hn => (splice_agrees q N n hn).symm)
    have hsecond := hsound (splice q N) (below q N) k z (splice_valid q N) (hbelow N) (he.symm.trans hr)
    exact False.elim (hdiff N (hfirst.symm.trans hsecond))

theorem below_bounds (q : ℚ) (N : ℕ) :
    (q:ℝ)-1/64 ≤ (below q N:ℝ) ∧ (below q N:ℝ) < q := by
  have hp : (0:ℝ) < radius N := by exact_mod_cast radius_pos N
  have hu : (radius N:ℝ) ≤ 1/32 := by
    have hh : (radius N:ℝ)*32 ≤ 1 := by
      exact_mod_cast (show radius N*32 ≤ 1 by have h := radius_small N; linarith)
    linarith
  simp only [below,Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat]
  constructor <;> linarith

theorem decimal_boundary : DigitExtraction.digits 10 (1/10) 0 = 1 := by
  norm_num [DigitExtraction.digits,DigitExtraction.remainder]

theorem decimal_below (N : ℕ) :
    (below (1/10) N:ℝ) ∈ Set.Ico 0 1 ∧
    DigitExtraction.digits 10 (below (1/10) N) 0 = 0 := by
  have hb := below_bounds (1/10) N
  norm_num at hb
  refine ⟨⟨by linarith,by linarith⟩,?_⟩
  simp only [DigitExtraction.digits,DigitExtraction.remainder,Nat.cast_ofNat]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num only [Int.cast_zero,zero_add] <;> linarith

/-- No universally correct canonical decimal reader can halt on this valid
boundary name, even if it may choose a different finite runtime on every name. -/
theorem decimal_cannot_halt {S : Type} (M : Machine S) (s : S)
    (hsound : ∀ I x k z, Valid I x → x ∈ Set.Ico 0 1 →
      run M I k s = some z → z=DigitExtraction.digits 10 x 0) :
    ∀ k, run M (straddle (1/10)) k s = none := by
  apply boundary_obstruction M s (fun x => DigitExtraction.digits 10 x 0)
    (1/10) (fun x => x∈Set.Ico 0 1) (by norm_num)
    (fun N => (decimal_below N).1) _ hsound
  intro N
  dsimp only
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  rw [decimal_boundary,(decimal_below N).2]
  norm_num

theorem no_total_decimal_reader {S : Type} (M : Machine S) (s : S) :
    ¬ ((∀ I x k z, Valid I x → x∈Set.Ico 0 1 →
          run M I k s=some z → z=DigitExtraction.digits 10 x 0) ∧
       (∀ I x, Valid I x → x∈Set.Ico 0 1 → ∃ k z, run M I k s=some z)) := by
  rintro ⟨hs,ht⟩
  obtain ⟨k,z,hz⟩ := ht (straddle (1/10)) (1/10) (by simpa using straddle_valid (1/10)) (by norm_num)
  rw [decimal_cannot_halt M s hs k] at hz
  contradiction

theorem cf_below (N : ℕ) : 0 < (below 1 N:ℝ) ∧ ⌊(below 1 N:ℝ)⌋ = (0:ℤ) := by
  have hb := below_bounds 1 N
  norm_num at hb
  refine ⟨by linarith,Int.floor_eq_iff.mpr ?_⟩
  norm_num only [Int.cast_zero,zero_add]
  exact ⟨by linarith,hb.2⟩

/-- The target is the actual first term of the canonical simple fraction. -/
theorem cf_head (x : ℝ) : (GenContFract.of x).h = (⌊x⌋:ℝ) :=
  GenContFract.of_h_eq_floor

theorem cf_cannot_halt {S : Type} (M : Machine S) (s : S)
    (hsound : ∀ I x k z, Valid I x → 0<x →
      run M I k s=some z → z=⌊x⌋) :
    ∀ k, run M (straddle 1) k s = none := by
  apply boundary_obstruction M s (fun x => ⌊x⌋) 1 (fun x => 0<x)
    (by norm_num) (fun N => (cf_below N).1) _ hsound
  intro N
  dsimp only
  rw [(cf_below N).2]
  norm_num

theorem no_total_cf_reader {S : Type} (M : Machine S) (s : S) :
    ¬ ((∀ I x k z, Valid I x → 0<x → run M I k s=some z → z=⌊x⌋) ∧
       (∀ I x, Valid I x → 0<x → ∃ k z, run M I k s=some z)) := by
  rintro ⟨hs,ht⟩
  obtain ⟨k,z,hz⟩ := ht (straddle 1) 1 (by simpa using straddle_valid 1) (by norm_num)
  rw [cf_cannot_halt M s hs k] at hz
  contradiction

/-- A positive result requiring an entire enclosing interval to fit in one
canonical digit cell. Touching the next boundary is deliberately insufficient. -/
theorem floor_certificate (I : QInterval) (x scale : ℝ) (z : ℤ)
    (hx : I.Contains x) (hs : 0 ≤ scale)
    (hl : (z:ℝ) ≤ scale*(I.lo:ℝ))
    (hu : scale*(I.hi:ℝ) < (z:ℝ)+1) : ⌊scale*x⌋=z := by
  apply Int.floor_eq_iff.mpr
  exact ⟨hl.trans (mul_le_mul_of_nonneg_left hx.1 hs),
    (mul_le_mul_of_nonneg_left hx.2 hs).trans_lt hu⟩

end GeneralizedIntervalArithmetic.FiniteQuery
