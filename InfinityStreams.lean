import ExceptionalComparisons
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Data.Real.Archimedean

/-! Tupper §2.6.3: rational sequences indexed by integers, exactly as in the
printed tail quantifiers. These are representation criteria, not IEEE casts. -/
namespace GeneralizedIntervalArithmetic.InfinityStreams
open Filter
open scoped Topology

def Up (x : ℤ → ℚ) : Prop := ∀ l : ℚ, ∃ j : ℤ, ∀ k : ℤ, j < k → l < x k
def Down (x : ℤ → ℚ) : Prop := ∀ l : ℚ, ∃ j : ℤ, ∀ k : ℤ, j < k → x k < l

/-- Strict `k > j` in the source is equivalent to the usual eventual tail. -/
theorem up_eventually (x : ℤ → ℚ) : Up x ↔ ∀ l : ℚ, ∀ᶠ k in atTop, l < x k := by
  constructor
  · intro h l
    obtain ⟨j, hj⟩ := h l
    exact eventually_atTop.2 ⟨j+1, fun k hk => hj k (by omega)⟩
  · intro h l
    obtain ⟨j, hj⟩ := eventually_atTop.1 (h l)
    exact ⟨j, fun k hk => hj k (le_of_lt hk)⟩

theorem down_eventually (x : ℤ → ℚ) : Down x ↔ ∀ l : ℚ, ∀ᶠ k in atTop, x k < l := by
  constructor
  · intro h l
    obtain ⟨j, hj⟩ := h l
    exact eventually_atTop.2 ⟨j+1, fun k hk => hj k (by omega)⟩
  · intro h l
    obtain ⟨j, hj⟩ := eventually_atTop.1 (h l)
    exact ⟨j, fun k hk => hj k (le_of_lt hk)⟩

theorem up_iff_rational_limit (x : ℤ → ℚ) : Up x ↔ Tendsto x atTop atTop := by
  rw [up_eventually, tendsto_atTop]
  constructor
  · intro h l
    filter_upwards [h l] with k hk using le_of_lt hk
  · intro h l
    filter_upwards [h (l+1)] with k hk
    linarith

theorem down_iff_rational_limit (x : ℤ → ℚ) : Down x ↔ Tendsto x atTop atBot := by
  rw [down_eventually, tendsto_atBot]
  constructor
  · intro h l
    filter_upwards [h l] with k hk using le_of_lt hk
  · intro h l
    filter_upwards [h (l-1)] with k hk
    linarith

/-- Rational threshold quantification suffices for every real threshold. -/
theorem up_iff_extended_limit (x : ℤ → ℚ) : Up x ↔
    Tendsto (fun k => ((x k : ℝ) : EReal)) atTop (𝓝 ⊤) := by
  rw [up_eventually, EReal.tendsto_nhds_top_iff_real]
  constructor
  · intro h r
    obtain ⟨q, hq⟩ := exists_rat_gt r
    filter_upwards [h q] with k hk
    exact EReal.coe_lt_coe_iff.mpr (hq.trans (by exact_mod_cast hk))
  · intro h q
    filter_upwards [h (q : ℝ)] with k hk
    exact_mod_cast EReal.coe_lt_coe_iff.mp hk

theorem down_iff_extended_limit (x : ℤ → ℚ) : Down x ↔
    Tendsto (fun k => ((x k : ℝ) : EReal)) atTop (𝓝 ⊥) := by
  rw [down_eventually, EReal.tendsto_nhds_bot_iff_real]
  constructor
  · intro h r
    obtain ⟨q, hq⟩ := exists_rat_lt r
    filter_upwards [h q] with k hk
    exact EReal.coe_lt_coe_iff.mpr ((by exact_mod_cast hk : (x k : ℝ) < q).trans hq)
  · intro h q
    filter_upwards [h (q : ℝ)] with k hk
    exact_mod_cast EReal.coe_lt_coe_iff.mp hk

theorem down_neg_iff (x : ℤ → ℚ) : Down (fun k => -x k) ↔ Up x := by
  constructor
  · intro h l
    obtain ⟨j, hj⟩ := h (-l)
    exact ⟨j, fun k hk => by have := hj k hk; dsimp at *; linarith⟩
  · intro h l
    obtain ⟨j, hj⟩ := h (-l)
    exact ⟨j, fun k hk => by have := hj k hk; dsimp at *; linarith⟩

theorem signs_exclusive (x : ℤ → ℚ) : ¬ (Up x ∧ Down x) := by
  rintro ⟨hu, hd⟩
  obtain ⟨j, hj⟩ := hu 0
  obtain ⟨i, hi⟩ := hd 0
  have h1 := hj (max i j + 1) (by omega)
  have h2 := hi (max i j + 1) (by omega)
  linarith

/-- Tail-equivalent presentations have the same signed representation criteria. -/
theorem eventual_agreement {x y : ℤ → ℚ} (h : x =ᶠ[atTop] y) :
    (Up x ↔ Up y) ∧ (Down x ↔ Down y) := by
  simp only [up_eventually, down_eventually]
  constructor <;> constructor <;> intro hh l
  all_goals filter_upwards [hh l, h] with k hk he
  all_goals simpa [he] using hk

/-- Explicit partial representation relation in the existing tagged carrier.
Lambda has no representation here; no total quotient construction is claimed. -/
def Represents (x : ℤ → ℚ) : ExceptionalComparisons.Value → Prop
  | .finite r => Tendsto (fun k => (x k : ℝ)) atTop (𝓝 r)
  | .posInf => Up x
  | .negInf => Down x
  | .undefined => False

/-- Exceptional tag promotion is exactly the already defined bound map, and
its representation criterion is convergence to that mapped bound. -/
theorem positive_promotion (x : ℤ → ℚ) :
    ExceptionalComparisons.bound .posInf = some (⊤ : EReal) ∧
    (Represents x .posInf ↔ Tendsto (fun k => ((x k : ℝ) : EReal)) atTop (𝓝 ⊤)) :=
  ⟨rfl, up_iff_extended_limit x⟩

theorem negative_promotion (x : ℤ → ℚ) :
    ExceptionalComparisons.bound .negInf = some (⊥ : EReal) ∧
    (Represents x .negInf ↔ Tendsto (fun k => ((x k : ℝ) : EReal)) atTop (𝓝 ⊥)) :=
  ⟨rfl, down_iff_extended_limit x⟩

theorem undefined_not_promoted (x : ℤ → ℚ) :
    ¬ Represents x .undefined ∧ ExceptionalComparisons.bound .undefined = none := ⟨id, rfl⟩

/-- Exact correspondence with the existing optional bound promotion. This is
not a numerical-comparison or arithmetic homomorphism theorem. -/
theorem represents_iff_limit (x : ℤ → ℚ) (v : ExceptionalComparisons.Value) :
    Represents x v ↔ ∃ b : EReal, ExceptionalComparisons.bound v = some b ∧
      Tendsto (fun k => ((x k : ℝ) : EReal)) atTop (𝓝 b) := by
  cases v with
  | finite r => simp [Represents, ExceptionalComparisons.bound, EReal.tendsto_coe]
  | negInf => simpa [Represents, ExceptionalComparisons.bound] using down_iff_extended_limit x
  | posInf => simpa [Represents, ExceptionalComparisons.bound] using up_iff_extended_limit x
  | undefined => simp [Represents, ExceptionalComparisons.bound]

/-- Uniqueness of an interpreted tag, not construction of a quotient carrier. -/
theorem representation_unique {x : ℤ → ℚ} {a b : ExceptionalComparisons.Value}
    (ha : Represents x a) (hb : Represents x b) : a = b := by
  obtain ⟨u, hu, htu⟩ := (represents_iff_limit x a).mp ha
  obtain ⟨v, hv, htv⟩ := (represents_iff_limit x b).mp hb
  have huv : u = v := tendsto_nhds_unique htu htv
  have he : ExceptionalComparisons.bound a = ExceptionalComparisons.bound b := by
    rw [hu, hv, huv]
  clear ha hb hu hv htu htv huv
  cases a <;> cases b <;> simp_all [ExceptionalComparisons.bound]

theorem integer_stream : Up (fun k : ℤ => (k : ℚ)) := by
  intro l
  obtain ⟨j, hj⟩ := exists_int_gt l
  exact ⟨j, fun k hk => hj.trans (by dsimp; exact_mod_cast hk)⟩

/-- Unbounded above on every tail, but returning to zero infinitely often. -/
def spikes (k : ℤ) : ℚ := if k % 2 = 0 then (k : ℚ) else 0

theorem spikes_tail_unbounded (l : ℚ) (j : ℤ) :
    ∃ k : ℤ, j < k ∧ l < spikes k := by
  obtain ⟨m, hm⟩ := exists_int_gt (max (j : ℚ) (max 0 l))
  have hj : (j : ℚ) < m := (le_max_left _ _).trans_lt hm
  have hz : (0 : ℚ) < m := (le_trans (le_max_left 0 l) (le_max_right _ _)).trans_lt hm
  have hl : l < (m : ℚ) := (le_trans (le_max_right 0 l) (le_max_right _ _)).trans_lt hm
  refine ⟨2*m, ?_, ?_⟩
  · have : (j : ℚ) < 2*m := by linarith
    exact_mod_cast this
  · simp [spikes]
    linarith

theorem spikes_not_up : ¬ Up spikes := by
  intro h
  obtain ⟨j, hj⟩ := h 0
  have hk : j < 2*(max j 0 + 1)+1 := by omega
  have := hj _ hk
  have hm : (2*(max j 0 + 1)+1) % 2 ≠ 0 := by omega
  simp only [spikes, if_neg hm, lt_self_iff_false] at this

theorem spikes_not_down : ¬ Down spikes := by
  intro h
  obtain ⟨j, hj⟩ := h 0
  obtain ⟨k, hk, hv⟩ := spikes_tail_unbounded 0 j
  have := hj k hk
  linarith

theorem spikes_unbounded : ¬ BddAbove (Set.range spikes) := by
  rintro ⟨b, hb⟩
  obtain ⟨k, _, hk⟩ := spikes_tail_unbounded b 0
  exact (not_le_of_gt hk) (hb (Set.mem_range_self k))

end GeneralizedIntervalArithmetic.InfinityStreams
