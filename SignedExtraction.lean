import RedundantCF
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Irrational

/-! A labeled nearest-integer construction for the printed signed restrictions.
Half-integer ties select the smaller integer. No floating-point rule is added. -/
namespace GeneralizedIntervalArithmetic.SignedExtraction
open Filter
open scoped Topology

section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

-- Keep executable specializations from introducing opaque compiler declarations
-- into the proof-audited namespace; the mathematical definitions are unchanged.
@[nospecialize]
def digit (x : K) : ℤ := ⌈x-1/2⌉
@[nospecialize]
def residual (x : K) : K := x-(digit x:K)
@[nospecialize]
def next (x : K) : K := 1/residual x

@[nospecialize]
def orbit (x : K) : ℕ → K
  | 0 => x
  | n+1 => next (orbit x n)

@[nospecialize]
def coeff (x : K) (n : ℕ) : ℤ := digit (orbit x n)

theorem residual_bounds (x : K) : -(1/2:K) < residual x ∧ residual x ≤ 1/2 := by
  have hl := Int.le_ceil (x-1/2)
  have hu := Int.ceil_lt_add_one (x-1/2)
  dsimp [residual,digit]
  constructor <;> linarith

omit [IsStrictOrderedRing K] in
theorem reconstruct_step (x : K) : x = (digit x:K)+1/next x := by
  simp [next,residual]

omit [IsStrictOrderedRing K] in
theorem orbit_shift (x : K) (n : ℕ) : orbit x (n+1)=orbit (next x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change next (orbit x (n+1)) = next (orbit (next x) n)
    rw [ih]

end Ordered

/-- Tail complete quotients are at least 2 or strictly below -2. -/
def Safe (x : ℝ) : Prop := 2≤x ∨ x < -2

theorem next_safe (x : ℝ) (hn : residual x ≠ 0) : Safe (next x) := by
  have hb := residual_bounds x
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · right
    exact (div_lt_iff_of_neg hneg).mpr (by linarith [hb.1])
  · left
    exact (le_div_iff₀ hpos).mpr (by linarith [hb.2])

theorem digit_pos {x : ℝ} (hx : 2≤x) : 2≤digit x := by
  have hb := (residual_bounds x).2
  have hh : (1:ℝ)<(digit x:ℝ) := by dsimp [residual] at hb; linarith
  have hi : (1:ℤ)<digit x := by exact_mod_cast hh
  omega

theorem digit_neg {x : ℝ} (hx : x < -2) : digit x ≤ -2 := by
  have hb := (residual_bounds x).1
  have hh : (digit x:ℝ)<(-1:ℝ) := by dsimp [residual] at hb; linarith
  have hi : digit x < (-1:ℤ) := by exact_mod_cast hh
  omega

theorem digit_large {x : ℝ} (hx : Safe x) : 2 ≤ |digit x| := by
  rcases hx with hx | hx
  · have h := digit_pos hx
    rw [abs_of_nonneg (by omega)]; exact h
  · have h := digit_neg hx
    rw [abs_of_nonpos (by omega)]; omega

theorem adjacent_sign {x : ℝ} (hx : Safe x) (hr : residual x ≠ 0)
    (ha : |digit x|=2) : 0 < digit x * digit (next x) := by
  rcases hx with hx | hx
  · have hp := digit_pos hx
    rw [abs_of_nonneg (by omega)] at ha
    have hrem : 0 < residual x := by
      have hh : 0 ≤ residual x := by dsimp [residual]; rw [ha]; norm_num; linarith
      exact lt_of_le_of_ne hh (Ne.symm hr)
    have hs := next_safe x hr
    have hn : 2 ≤ next x := by
      rcases hs with hs | hs
      · exact hs
      · have : 0 < next x := one_div_pos.mpr hrem
        linarith
    have hnext := digit_pos hn
    rw [ha]; omega
  · have hp := digit_neg hx
    rw [abs_of_nonpos (by omega)] at ha
    have he : digit x = -2 := by omega
    have hrem : residual x < 0 := by dsimp [residual]; rw [he]; norm_num; linarith
    have hs := next_safe x hr
    have hn : next x < -2 := by
      rcases hs with hs | hs
      · have : next x < 0 := one_div_neg.mpr hrem
        linarith
      · exact hs
    have hnext := digit_neg hn
    rw [he]; omega

/-- No stopping residual: the generated stream is genuinely infinite. -/
def NeverStops (x : ℝ) : Prop := ∀n, residual (orbit x n) ≠ 0

theorem infinite_admissible {x : ℝ} (hx : NeverStops x) : RedundantCF.Admissible (coeff x) := by
  constructor
  · intro n
    exact digit_large (next_safe (orbit x n) (hx n))
  · intro n hn
    exact adjacent_sign (next_safe (orbit x n) (hx n)) (hx (n+1)) hn

/-- Direct comparison with the already defined finite nested observations. -/
theorem observation_error {x : ℝ} (hx : NeverStops x) (n k : ℕ) :
    |orbit x n - (InfiniteSimpleCF.trunc (coeff x) n k:ℝ)| ≤ (4/9:ℝ)^k := by
  have ha := infinite_admissible hx
  induction k generalizing n with
  | zero =>
    have hb := residual_bounds (orbit x n)
    have hh : |residual (orbit x n)| ≤ (1/2:ℝ) := abs_le.mpr ⟨hb.1.le,hb.2⟩
    simpa [InfiniteSimpleCF.trunc,coeff,residual] using hh.trans (by norm_num : (1/2:ℝ)≤1)
  | succ k ih =>
    have hb := residual_bounds (orbit x (n+1))
    have hres : |residual (orbit x (n+1))| ≤ (1/2:ℝ) := abs_le.mpr ⟨hb.1.le,hb.2⟩
    have hc : (2:ℝ)≤|(coeff x (n+1):ℝ)| := by exact_mod_cast ha.1 n
    have hstep := RedundantCF.step_contract hc hres (RedundantCF.fraction_invariant ha (n+1) k).1
    have hr := reconstruct_step (orbit x n)
    have he : orbit x (n+1) = (coeff x (n+1):ℝ)+residual (orbit x (n+1)) := by simp [residual,coeff]
    have ht := InfiniteSimpleCF.trunc_fraction (coeff x) (n+1) k
    have hi := ih (n+1)
    rw [he,ht,add_sub_add_left_eq_sub] at hi
    rw [show orbit x n = (coeff x n:ℝ)+1/orbit x (n+1) from hr,
      InfiniteSimpleCF.trunc]
    push_cast
    rw [add_sub_add_left_eq_sub,he,ht]
    apply hstep.trans
    rw [pow_succ]
    nlinarith

theorem infinite_recovers {x : ℝ} (hx : NeverStops x) :
    RedundantCF.Represents (coeff x) x := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤4/9) (by norm_num : (4/9:ℝ)<1)
  obtain ⟨N,hN⟩ := (hg.eventually (gt_mem_nhds hε)).exists
  refine ⟨N,?_⟩
  intro n hn
  have he := observation_error hx 0 n
  have hp : (4/9:ℝ)^n ≤ (4/9:ℝ)^N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hd : dist ((InfiniteSimpleCF.trunc (coeff x) 0 n):ℝ) x ≤ (4/9:ℝ)^n := by
    simpa [Real.dist_eq,abs_sub_comm,orbit] using he
  exact hd.trans_lt (hp.trans_lt hN)

/-- First zero residual, so all earlier divisions are genuinely defined. -/
def FirstStop (x : ℝ) (n : ℕ) : Prop :=
  residual (orbit x n)=0 ∧ ∀ k, k<n → residual (orbit x k)≠0

def segment (a : ℕ → ℤ) (start : ℕ) : ℕ → List ℤ
  | 0 => []
  | n+1 => a start :: segment a (start+1) n

theorem segment_eq_map (a : ℕ → ℤ) (start n : ℕ) :
    segment a start n = (List.range n).map (fun j => a (start+j)) := by
  induction n generalizing start with
  | zero => simp [segment]
  | succ n ih =>
    simp only [segment,ih,List.range_succ_eq_map,List.map_cons,List.map_map,
      Function.comp_def,Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    congr 1; omega

theorem segment_valid (a : ℕ → ℤ) (start n : ℕ)
    (hl : ∀ i, i<n → 2≤|a (start+i)|)
    (hs : ∀ i, i+1<n → |a (start+i)|=2 → 0<a (start+i)*a (start+i+1))
    (he : ∀ i, i+1=n → a (start+i)≠-2) :
    RedundantCF.FiniteTail (segment a start n) := by
  induction n generalizing start with
  | zero => simp [segment,RedundantCF.FiniteTail]
  | succ n ih =>
    cases n with
    | zero => simpa [segment,RedundantCF.FiniteTail] using he 0 rfl
    | succ n =>
      change 2≤|a start| ∧ (|a start|=2 → 0<a start*a (start+1)) ∧
        RedundantCF.FiniteTail (segment a (start+1) (n+1))
      refine ⟨by simpa using hl 0 (by omega),by simpa using hs 0 (by omega),?_⟩
      apply ih
      · intro i hi
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hl (i+1) (by omega)
      · intro i hi
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs (i+1) (by omega)
      · intro i hi
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he (i+1) (by omega)

theorem stopped_tail_safe {x : ℝ} {n : ℕ} (hx : FirstStop x n)
    (j : ℕ) (hj : j<n) : Safe (orbit x (j+1)) :=
  next_safe (orbit x j) (hx.2 j hj)

theorem finite_admissible {x : ℝ} {n : ℕ} (hx : FirstStop x n) :
    RedundantCF.FiniteTail (segment (coeff x) 1 n) := by
  apply segment_valid
  · intro i hi
    simpa [coeff,Nat.add_comm] using digit_large (stopped_tail_safe hx i hi)
  · intro i hi
    have h := adjacent_sign (stopped_tail_safe hx i (by omega)) (hx.2 (i+1) hi)
    simpa [coeff,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
  · intro i hi he
    have hs := stopped_tail_safe hx i (by omega)
    have ht := hx.1
    have hd : (digit (orbit x n):ℝ)=orbit x n := by dsimp [residual] at ht; linarith
    have ha : digit (orbit x n)=-2 := by simpa [coeff,←hi,Nat.add_comm] using he
    rw [ha] at hd
    have hh : orbit x n = -2 := by simpa using hd.symm
    rw [hi] at hs
    rcases hs with hs | hs <;> linarith

/-- A terminal integer recovers every finite suffix. Definedness of intermediate
reciprocals is provided by FirstStop and stopped_tail_safe, not totalized zero. -/
theorem stopped_suffix_exact (x : ℝ) (start k : ℕ)
    (ht : residual (orbit x (start+k))=0) :
    (InfiniteSimpleCF.trunc (coeff x) start k:ℝ)=orbit x start := by
  induction k generalizing start with
  | zero =>
    simp only [Nat.add_zero] at ht
    simp only [InfiniteSimpleCF.trunc,Rat.cast_intCast,coeff]
    dsimp [residual] at ht
    linarith
  | succ k ih =>
    have hh : residual (orbit x (start+1+k))=0 := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht
    simp only [InfiniteSimpleCF.trunc,Rat.cast_add,Rat.cast_intCast,Rat.cast_div,Rat.cast_one]
    rw [ih (start+1) hh]
    exact (reconstruct_step (orbit x start)).symm

theorem finite_recovers {x : ℝ} {n : ℕ} (hx : FirstStop x n) :
    (ContinuedFractionConversion.finiteValue (coeff x 0)
      ((segment (coeff x) 1 n).map (fun a : ℤ => (a:ℚ))):ℝ)=x := by
  have he := InfiniteSimpleCF.trunc_finite (coeff x) 0 n
  simp only [Nat.zero_add] at he
  have hm : (segment (coeff x) 1 n).map (fun a : ℤ => (a:ℚ)) =
      (List.range n).map (fun j => (coeff x (j+1):ℚ)) := by
    rw [segment_eq_map,List.map_map]
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply,Nat.add_comm]
  rw [hm,←he]
  exact stopped_suffix_exact x 0 n (by simpa using hx.1)

theorem finite_divisors_nonzero {x : ℝ} {n : ℕ} (hx : FirstStop x n)
    (j : ℕ) (hj : j<n) :
    (InfiniteSimpleCF.trunc (coeff x) (j+1) (n-(j+1)):ℝ) ≠ 0 := by
  rw [stopped_suffix_exact x (j+1) (n-(j+1)) (by simpa [Nat.add_sub_of_le (show j+1≤n by omega)] using hx.1)]
  have hs := stopped_tail_safe hx j hj
  rcases hs with hs | hs <;> linarith

/-- Mathematical coverage of every real by a valid finite expansion or the
proved infinite signed semantics. No uniqueness or interval-oracle algorithm. -/
theorem coverage (x : ℝ) :
    (∃ n, FirstStop x n ∧ RedundantCF.FiniteTail (segment (coeff x) 1 n) ∧
      (ContinuedFractionConversion.finiteValue (coeff x 0)
        ((segment (coeff x) 1 n).map (fun a : ℤ => (a:ℚ))):ℝ)=x) ∨
    (RedundantCF.Admissible (coeff x) ∧ RedundantCF.Represents (coeff x) x) := by
  classical
  by_cases hx : NeverStops x
  · exact Or.inr ⟨infinite_admissible hx,infinite_recovers hx⟩
  · have he : ∃n, residual (orbit x n)=0 := by simpa [NeverStops] using hx
    let n := Nat.find he
    have hs : FirstStop x n := ⟨Nat.find_spec he,fun k hk => Nat.find_min he hk⟩
    exact Or.inl ⟨n,hs,finite_admissible hs,finite_recovers hs⟩

theorem digit_cast (q : ℚ) : digit (q:ℝ)=digit q := by
  unfold digit
  have h := Rat.ceil_cast (α:=ℝ) (q-1/2)
  simpa using h

theorem residual_cast (q : ℚ) : residual (q:ℝ)=(residual (K:=ℚ) q:ℝ) := by
  simp [residual,digit_cast]

theorem next_cast (q : ℚ) : next (q:ℝ)=(next (K:=ℚ) q:ℝ) := by
  simp [next,residual_cast]

theorem orbit_cast (q : ℚ) (n : ℕ) : orbit (q:ℝ) n=(orbit (K:=ℚ) q n:ℝ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orbit,ih,next_cast]

/-- Strict rational denominator descent, with no particular rational syntax
or gcd normalization trusted beyond the existing Rat theorems. -/
theorem next_den_lt (q : ℚ) (hr : residual q ≠ 0) : (next q).den < q.den := by
  let m : ℤ := q.num-digit q*(q.den:ℤ)
  have hd : (0:ℚ)<q.den := by exact_mod_cast q.pos
  have hm : (m:ℚ)=residual q*(q.den:ℚ) := by
    dsimp [m,residual]
    push_cast
    rw [sub_mul,Rat.mul_den_eq_num]
  have hm0 : m ≠ 0 := by
    intro hz
    have hh : (m:ℚ)=0 := by rw [hz]; norm_num
    rw [hm] at hh
    exact (mul_ne_zero hr (ne_of_gt hd)) hh
  have hb := residual_bounds q
  have he : |residual q| < (1:ℚ) := abs_lt.mpr ⟨by linarith [hb.1],by linarith [hb.2]⟩
  have hmabs : (m.natAbs:ℚ) < q.den := by
    have hh : |(m:ℚ)|=|residual q| * (q.den:ℚ) := by rw [hm,abs_mul,abs_of_pos hd]
    have hh' : |(m:ℚ)| < (q.den:ℚ) := by rw [hh]; nlinarith
    rw [Int.cast_natAbs,Int.cast_abs]
    exact hh'
  have hmn : m.natAbs < q.den := by exact_mod_cast hmabs
  have hrepr : next q = Rat.divInt (q.den:ℤ) m := by
    rw [Rat.divInt_eq_div]
    dsimp [next]
    push_cast
    rw [hm]
    field_simp
  have hden : (next q).den ≤ m.natAbs := by
    rw [hrepr,Rat.den_mk,if_neg hm0]
    exact Nat.div_le_self _ _
  exact hden.trans_lt hmn

/-- A concrete denominator bound on a stopping index, not merely Nat.find
existence. This supplies fuel to an executable rational observation routine. -/
theorem rational_stops (q : ℚ) : ∃ n < q.den, residual (orbit q n)=0 := by
  induction hd : q.den using Nat.strong_induction_on generalizing q with
  | h d ih =>
    by_cases hr : residual q=0
    · exact ⟨0,by simpa [hd] using q.pos,hr⟩
    · have hlt := next_den_lt q hr
      obtain ⟨n,hn,he⟩ := ih (next q).den (by simpa [hd] using hlt) (next q) rfl
      refine ⟨n+1,by omega,?_⟩
      rw [orbit_shift]
      exact he

/-- The real orbit of a rational input terminates too: the conversion bridge
is proved, not an assumed relation between two independently defined algorithms. -/
theorem rational_real_stops (q : ℚ) : ∃n < q.den, residual (orbit (q:ℝ) n)=0 := by
  obtain ⟨n,hn,he⟩ := rational_stops q
  refine ⟨n,hn,?_⟩
  rw [orbit_cast,residual_cast,he]
  norm_num

theorem coeff_cast (q : ℚ) : coeff (q:ℝ)=coeff q := by
  funext n
  simp [coeff,orbit_cast,digit_cast]

/-- Bounded executable rational search. Fuel exhaustion is not a semantic value. -/
def findStop (q : ℚ) : ℕ → Option ℕ
  | 0 => none
  | fuel+1 => if residual q=0 then some 0 else
      (findStop (next q) fuel).map Nat.succ

theorem findStop_spec (q : ℚ) (fuel n : ℕ) (h : findStop q fuel=some n) :
    n<fuel ∧ residual (orbit q n)=0 ∧
      ∀ j, j<n → residual (orbit q j)≠0 := by
  induction fuel generalizing q n with
  | zero => simp [findStop] at h
  | succ fuel ih =>
    by_cases hr : residual q=0
    · simp [findStop,hr] at h
      subst n
      exact ⟨by omega,hr,by intro j hj; omega⟩
    · cases he : findStop (next q) fuel with
      | none => simp [findStop,hr,he] at h
      | some m =>
        simp only [findStop,hr,↓reduceIte,he,Option.map_some,Option.some.injEq] at h
        change some (m+1) = some n at h
        have hmn : m+1=n := Option.some.inj h
        subst n
        obtain ⟨hm,hstop,hpre⟩ := ih (next q) m he
        refine ⟨by omega,?_,?_⟩
        · simpa only [orbit_shift] using hstop
        · intro j hj
          cases j with
          | zero => exact hr
          | succ j => simpa only [orbit_shift] using hpre j (by omega)

theorem findStop_complete (q : ℚ) (fuel : ℕ)
    (h : ∃ n<fuel, residual (orbit q n)=0) : ∃ n, findStop q fuel=some n := by
  induction fuel generalizing q with
  | zero => obtain ⟨n,hn,_⟩ := h; omega
  | succ fuel ih =>
    by_cases hr : residual q=0
    · exact ⟨0,by simp [findStop,hr]⟩
    · obtain ⟨n,hn,he⟩ := h
      cases n with
      | zero => exact False.elim (hr he)
      | succ n =>
        obtain ⟨m,hm⟩ := ih (next q) ⟨n,by omega,by simpa only [orbit_shift] using he⟩
        exact ⟨m+1,by simp [findStop,hr,hm]⟩

def extract (q : ℚ) : Option (ℤ × List ℤ) :=
  (findStop q q.den).map (fun n => (coeff q 0,segment (coeff q) 1 n))

/-- Executable rational extraction succeeds within the original denominator
bound, obeys the printed finite restrictions and decodes exactly to its input. -/
theorem rational_extracts (q : ℚ) : ∃ a bs,
    extract q=some (a,bs) ∧ RedundantCF.FiniteTail bs ∧
      ContinuedFractionConversion.finiteValue (a:ℚ) (bs.map (fun b : ℤ => (b:ℚ)))=q := by
  obtain ⟨n,hn⟩ := findStop_complete q q.den (rational_stops q)
  obtain ⟨_,hs,hpre⟩ := findStop_spec q q.den n hn
  have hreal : FirstStop (q:ℝ) n := by
    constructor
    · rw [orbit_cast,residual_cast,hs]; norm_num
    · intro j hj
      rw [orbit_cast,residual_cast]
      exact_mod_cast hpre j hj
  refine ⟨coeff q 0,segment (coeff q) 1 n,by simp [extract,hn],?_,?_⟩
  · simpa only [coeff_cast] using finite_admissible hreal
  · have he := finite_recovers hreal
    rw [coeff_cast] at he
    exact_mod_cast he

/-- The generated orbit terminates exactly for rational inputs. This does not
claim uniqueness or irrationality for every arbitrary signed presentation. -/
theorem stops_iff_rational (x : ℝ) :
    (∃ n, residual (orbit x n)=0) ↔ ∃ q:ℚ, x=(q:ℝ) := by
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨InfiniteSimpleCF.trunc (coeff x) 0 n,
      (stopped_suffix_exact x 0 n (by simpa using hn)).symm⟩
  · rintro ⟨q,rfl⟩
    obtain ⟨n,_,hn⟩ := rational_real_stops q
    exact ⟨n,hn⟩

theorem never_stops_iff_irrational (x : ℝ) :
    NeverStops x ↔ ¬∃q:ℚ, x=(q:ℝ) := by
  rw [←stops_iff_rational]
  simp [NeverStops]

end GeneralizedIntervalArithmetic.SignedExtraction
