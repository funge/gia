import Evaluator
import ReciprocalStreams
import Mathlib.Topology.Algebra.Order.Field

namespace GeneralizedIntervalArithmetic.ExpressionStreams
open Filter
open scoped Topology

/-- Both rational endpoints, interpreted in ℝ, converge to the same value.
Ordering is supplied by QInterval; neither nesting nor a rate is assumed. -/
def Converges (I : ℕ → QInterval) (z : ℝ) : Prop :=
  Tendsto (fun n => ((I n).lo : ℝ)) atTop (𝓝 z) ∧
  Tendsto (fun n => ((I n).hi : ℝ)) atTop (𝓝 z)

theorem point_converges (q : ℚ) : Converges (fun _ => QInterval.point q) q :=
  ⟨tendsto_const_nhds,tendsto_const_nhds⟩

theorem add_converges {I J : ℕ → QInterval} {x y : ℝ}
    (hi : Converges I x) (hj : Converges J y) :
    Converges (fun n => (I n).add (J n)) (x+y) := by
  exact ⟨by simpa [QInterval.add] using hi.1.add hj.1,
    by simpa [QInterval.add] using hi.2.add hj.2⟩

theorem sub_converges {I J : ℕ → QInterval} {x y : ℝ}
    (hi : Converges I x) (hj : Converges J y) :
    Converges (fun n => (I n).sub (J n)) (x-y) := by
  exact ⟨by simpa [QInterval.sub] using hi.1.sub hj.2,
    by simpa [QInterval.sub] using hi.2.sub hj.1⟩

theorem mul_converges {I J : ℕ → QInterval} {x y : ℝ}
    (hi : Converges I x) (hj : Converges J y) :
    Converges (fun n => (I n).mul (J n)) (x*y) := by
  constructor
  · simpa [QInterval.mul] using
      ((hi.1.mul hj.1).min (hi.1.mul hj.2)).min ((hi.2.mul hj.1).min (hi.2.mul hj.2))
  · simpa [QInterval.mul] using
      ((hi.1.mul hj.1).max (hi.1.mul hj.2)).max ((hi.2.mul hj.1).max (hi.2.mul hj.2))

/-- A total bookkeeping stream only. The dummy prefix is never an evaluator
success or a semantic value at an undefined input. -/
def reciprocalTail (I : QInterval) : QInterval :=
  if h : I.AwayZero then I.recip h else QInterval.point 0

theorem eventually_away {I : ℕ → QInterval} {z : ℝ}
    (hi : Converges I z) (hz : z ≠ 0) : ∀ᶠ n in atTop, (I n).AwayZero := by
  have hs := ReciprocalStreams.eventually_success hi.1 hi.2 hz
    (fun n => by exact_mod_cast (I n).ordered)
  filter_upwards [hs] with n hn
  unfold ReciprocalStreams.evaluate at hn
  split_ifs at hn with h
  · rcases h.2 with hp | hn
    · exact Or.inr (by exact_mod_cast hp)
    · exact Or.inl (by exact_mod_cast hn)

theorem recip_converges {I : ℕ → QInterval} {z : ℝ}
    (hi : Converges I z) (hz : z ≠ 0) :
    Converges (fun n => reciprocalTail (I n)) z⁻¹ := by
  have he := eventually_away hi hz
  constructor
  · apply (hi.2.inv₀ hz).congr'
    filter_upwards [he] with n hn
    simp [reciprocalTail,hn,QInterval.recip]
  · apply (hi.1.inv₀ hz).congr'
    filter_upwards [he] with n hn
    simp [reciprocalTail,hn,QInterval.recip]

/-- The existing finite Expr grammar and strict Value derivation are reused.
Every division node in Value carries its actual nonzero denominator premise. -/
theorem eval_converges {X Y : ℕ → QInterval} {x y z : ℝ} {e : Expr}
    (hx : Converges X x) (hy : Converges Y y) (hv : Value x y e z) :
    ∃ R : ℕ → QInterval, Converges R z ∧
      ∀ᶠ n in atTop, eval exactBackend (X n) (Y n) e = some (R n) := by
  induction hv with
  | const q => exact ⟨fun _ => .point q, point_converges q, Eventually.of_forall (fun _ => rfl)⟩
  | x => exact ⟨X,hx,Eventually.of_forall (fun _ => rfl)⟩
  | y => exact ⟨Y,hy,Eventually.of_forall (fun _ => rfl)⟩
  | add ha hb iha ihb =>
    obtain ⟨I,hi,hei⟩ := iha
    obtain ⟨J,hj,hej⟩ := ihb
    refine ⟨fun n => (I n).add (J n),add_converges hi hj,?_⟩
    filter_upwards [hei,hej] with n hn hm
    simp only [eval,hn,hm]
    rfl
  | sub ha hb iha ihb =>
    obtain ⟨I,hi,hei⟩ := iha
    obtain ⟨J,hj,hej⟩ := ihb
    refine ⟨fun n => (I n).sub (J n),sub_converges hi hj,?_⟩
    filter_upwards [hei,hej] with n hn hm
    simp only [eval,hn,hm]
    rfl
  | mul ha hb iha ihb =>
    obtain ⟨I,hi,hei⟩ := iha
    obtain ⟨J,hj,hej⟩ := ihb
    refine ⟨fun n => (I n).mul (J n),mul_converges hi hj,?_⟩
    filter_upwards [hei,hej] with n hn hm
    simp only [eval,hn,hm]
    rfl
  | div ha hb hz iha ihb =>
    obtain ⟨I,hi,hei⟩ := iha
    obtain ⟨J,hj,hej⟩ := ihb
    refine ⟨fun n => (I n).mul (reciprocalTail (J n)),?_,?_⟩
    · simpa [div_eq_mul_inv] using mul_converges hi (recip_converges hj hz)
    · filter_upwards [hei,hej,eventually_away hj hz] with n hn hm hg
      simp only [eval,hn,hm]
      simp [combine,exactBackend,guardedDiv,reciprocalTail,hg]

/-- Enclosure uses the already-proved evaluator theorem, at the same n for
both variables and all occurrences. It is not a Cartesian independence claim. -/
theorem eval_converges_encloses {X Y : ℕ → QInterval} {x y z : ℝ} {e : Expr}
    (hx : Converges X x) (hy : Converges Y y) (hv : Value x y e z) :
    ∃ R : ℕ → QInterval, Converges R z ∧
      ∀ᶠ n in atTop, eval exactBackend (X n) (Y n) e = some (R n) ∧
        ∀ a b v : ℝ, (X n).Contains a → (Y n).Contains b →
          Value a b e v → (R n).Contains v := by
  obtain ⟨R,hr,he⟩ := eval_converges hx hy hv
  refine ⟨R,hr,?_⟩
  filter_upwards [he] with n hn
  exact ⟨hn,fun _ _ _ ha hb hv => eval_sound exactBackend_sound ha hb hv _ hn⟩

theorem eventual_width {I : ℕ → QInterval} {z ε : ℝ}
    (hi : Converges I z) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ((I n).hi : ℝ) - (I n).lo < ε := by
  have h : Tendsto (fun n => ((I n).hi : ℝ) - (I n).lo) atTop (𝓝 0) := by
    simpa using hi.2.sub hi.1
  exact h.eventually_lt_const hε

/-- An executable exact-rational acceptance test, not a modulus or a search
implementation. Rejection includes evaluator failure. -/
def precisionTest (q : ℚ) : Option QInterval → Bool
  | none => false
  | some I => decide (I.hi-I.lo < q)

theorem eventually_precision {X Y : ℕ → QInterval} {x y z : ℝ} {e : Expr}
    (hx : Converges X x) (hy : Converges Y y) (hv : Value x y e z)
    {q : ℚ} (hq : 0 < q) :
    ∀ᶠ n in atTop, precisionTest q (eval exactBackend (X n) (Y n) e) = true := by
  obtain ⟨R,hr,he⟩ := eval_converges hx hy hv
  have hw := eventual_width hr (show (0:ℝ) < q by exact_mod_cast hq)
  filter_upwards [he,hw] with n hn hm
  rw [hn]
  simp only [precisionTest,decide_eq_true_eq]
  exact_mod_cast hm

theorem exists_precision {X Y : ℕ → QInterval} {x y z : ℝ} {e : Expr}
    (hx : Converges X x) (hy : Converges Y y) (hv : Value x y e z)
    {q : ℚ} (hq : 0 < q) :
    ∃ n, precisionTest q (eval exactBackend (X n) (Y n) e) = true :=
  (eventually_precision hx hy hv hq).exists

/-- A passed width test bounds the error of every point in the returned interval,
provided the same inputs enclose the actual value. No endpoint attainment claimed. -/
theorem precision_sound {X Y : QInterval} {x y z w : ℝ} {e : Expr} {q : ℚ}
    (hx : X.Contains x) (hy : Y.Contains y) (hv : Value x y e z)
    {I : QInterval} (he : eval exactBackend X Y e = some I)
    (hp : precisionTest q (some I) = true) (hw : I.Contains w) :
    |w-z| < (q:ℝ) := by
  have hz := eval_sound exactBackend_sound hx hy hv I he
  have hq : I.hi-I.lo < q := by simpa [precisionTest] using hp
  have hq' : (I.hi:ℝ)-(I.lo:ℝ) < q := by exact_mod_cast hq
  apply abs_lt.mpr
  constructor <;> linarith [hw.1,hw.2,hz.1,hz.2]

/-- Classical ε corollary for the limit, with explicit input enclosure. -/
theorem eventual_accuracy {X Y : ℕ → QInterval} {x y z ε : ℝ} {e : Expr}
    (hx : Converges X x) (hy : Converges Y y) (hv : Value x y e z)
    (hX : ∀ n, (X n).Contains x) (hY : ∀ n, (Y n).Contains y) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ I, eval exactBackend (X n) (Y n) e = some I ∧
      I.Contains z ∧ ∀ w, I.Contains w → |w-z| < ε := by
  obtain ⟨R,hr,he⟩ := eval_converges hx hy hv
  filter_upwards [he,eventual_width hr hε] with n hn hm
  have hz := eval_sound exactBackend_sound (hX n) (hY n) hv (R n) hn
  refine ⟨R n,hn,hz,?_⟩
  intro w hw
  apply abs_lt.mpr
  constructor <;> linarith [hw.1,hw.2,hz.1,hz.2]

/-- Exact-rational sequential search, using the existing evaluator. Its
termination proof is the convergence theorem; it supplies no a priori rate.
Executable use requires executable total input streams and a positive rational
query. This is not hardware arbitrary precision or a new interval evaluator. -/
def firstPrecision (X Y : ℕ → QInterval) {x y z : ℝ} (e : Expr)
    (hx : Converges X x) (hy : Converges Y y) (hv : Value x y e z)
    (q : ℚ) (hq : 0 < q) : ℕ :=
  Nat.find (exists_precision hx hy hv hq)

theorem firstPrecision_passes (X Y : ℕ → QInterval) {x y z : ℝ} (e : Expr)
    (hx : Converges X x) (hy : Converges Y y) (hv : Value x y e z)
    (q : ℚ) (hq : 0 < q) :
    precisionTest q (eval exactBackend (X (firstPrecision X Y e hx hy hv q hq))
      (Y (firstPrecision X Y e hx hy hv q hq)) e) = true :=
  Nat.find_spec (exists_precision hx hy hv hq)

theorem firstPrecision_certificate (X Y : ℕ → QInterval) {x y z : ℝ} (e : Expr)
    (hx : Converges X x) (hy : Converges Y y) (hv : Value x y e z)
    (hX : ∀ n, (X n).Contains x) (hY : ∀ n, (Y n).Contains y)
    (q : ℚ) (hq : 0 < q) :
    let n := firstPrecision X Y e hx hy hv q hq
    ∃ I, eval exactBackend (X n) (Y n) e = some I ∧
      I.Contains z ∧ ∀ w, I.Contains w → |w-z| < (q:ℝ) := by
  dsimp only
  have hp := firstPrecision_passes X Y e hx hy hv q hq
  cases he : eval exactBackend (X (firstPrecision X Y e hx hy hv q hq))
      (Y (firstPrecision X Y e hx hy hv q hq)) e with
  | none => simp [he,precisionTest] at hp
  | some I =>
    rw [he] at hp
    exact ⟨I,rfl,eval_sound exactBackend_sound (hX _) (hY _) hv _ he,
      fun _ hw => precision_sound (hX _) (hY _) hv he hp hw⟩

end GeneralizedIntervalArithmetic.ExpressionStreams
