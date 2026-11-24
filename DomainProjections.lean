import DomainConstraints
import SquareRootDomains

/-! Finite Boolean projections (§2.7.2) and numeric domain descriptions (§2.11).
Exact classifier images justify numeric widening; endpoint samples alone do not. -/
namespace GeneralizedIntervalArithmetic.DomainProjections
open StrictComparison BooleanComposition DomainConstraints

/-- Source pessimistic projection is the already existing lower Boolean bound. -/
theorem pessimistic_iff (v : Truth) : v.lower = true ↔ ∀ b ∈ v.values, b = true := by
  cases v <;> simp [Truth.lower, Truth.values, Bool.forall_bool]

/-- Source optimistic projection is the already existing upper Boolean bound. -/
theorem optimistic_iff (v : Truth) : v.upper = true ↔ true ∈ v.values := by
  cases v <;> simp [Truth.upper, Truth.values]

theorem lower_implies_upper (v : Truth) : v.lower = true → v.upper = true := by
  cases v <;> simp [Truth.lower, Truth.upper]

/-- Interpret any conservative Boolean description as definite/possible domain bounds. -/
def domain {α : Type*} (v : α → Truth) : DomainBounds α :=
  ⟨fun p => (v p).lower = true, fun p => (v p).upper = true,
    fun p => lower_implies_upper (v p)⟩

theorem description_domain {α : Type*} (v : α → Truth) (p : α) :
    description (domain v) p = v p := by
  cases h : v p <;> simp [description, domain, h, Truth.lower, Truth.upper]

theorem domain_compatible {α : Type*} (v : α → Truth) (p : α)
    (P : Prop) [Decidable P] :
    (domain v).Compatible p P ↔ decide P ∈ (v p).values := by
  rw [← description_compatible, description_domain]

theorem domain_refines {α : Type*} {v w : α → Truth}
    (h : ∀ p, (v p).Refines (w p)) : Refines (domain v) (domain w) := by
  intro p
  constructor
  · intro hw
    change (w p).lower = true at hw
    change (v p).lower = true
    rw [pessimistic_iff] at hw ⊢
    exact fun b hb => hw b (h p hb)
  · intro hv
    change (v p).upper = true at hv
    change (w p).upper = true
    rw [optimistic_iff] at hv ⊢
    exact h p hv

/-- Non-strict comparison is the complement of the reversed strict comparison. -/
def compareLE (I J : QInterval) : Truth := neg (StrictComparison.compare J I)

noncomputable def leOutcomes (I J : QInterval) : Set Bool := by
  classical
  exact {b | ∃ x y : ℝ, I.Contains x ∧ J.Contains y ∧ decide (x ≤ y) = b}

theorem compareLE_exact (I J : QInterval) :
    (compareLE I J).values = leOutcomes I J := by
  classical
  rw [compareLE, comparison_neg_exact]
  ext b
  constructor
  · rintro ⟨c, ⟨y, x, hy, hx, hc⟩, rfl⟩
    refine ⟨x, y, hx, hy, ?_⟩
    rw [← hc]
    by_cases hxy : x ≤ y
    · simp [hxy, not_lt.mpr hxy]
    · simp [hxy, lt_of_not_ge hxy]
  · rintro ⟨x, y, hx, hy, rfl⟩
    refine ⟨decide (y < x), ⟨y, x, hy, hx, rfl⟩, ?_⟩
    by_cases hxy : x ≤ y
    · simp [hxy, not_lt.mpr hxy]
    · simp [hxy, lt_of_not_ge hxy]

theorem compareLE_true_iff (I J : QInterval) :
    compareLE I J = .trueOnly ↔ I.hi ≤ J.lo := by
  unfold compareLE
  have : ∀ v : Truth, neg v = .trueOnly ↔ v = .falseOnly := by intro v; cases v <;> simp [neg]
  rw [this, compare_false_iff]

theorem compareLE_false_iff (I J : QInterval) :
    compareLE I J = .falseOnly ↔ J.hi < I.lo := by
  unfold compareLE
  have : ∀ v : Truth, neg v = .falseOnly ↔ v = .trueOnly := by intro v; cases v <;> simp [neg]
  rw [this, compare_true_iff]

/-- Whole interval image, not merely endpoint classifications. -/
def numericImage (f : ℝ → Bool) (I : QInterval) : Set Bool :=
  {b | ∃ x, I.Contains x ∧ f x = b}

theorem numeric_refines (f : ℝ → Bool) (classify : QInterval → Truth)
    (exactImage : ∀ I, (classify I).values = numericImage f I)
    {I J : QInterval} (h : ∀ x, I.Contains x → J.Contains x) :
    (classify I).Refines (classify J) := by
  rw [Truth.Refines, exactImage, exactImage]
  rintro b ⟨x, hx, hb⟩
  exact ⟨x, h x hx, hb⟩

theorem numeric_projections (f : ℝ → Bool) (classify : QInterval → Truth)
    (exactImage : ∀ I, (classify I).values = numericImage f I) (I : QInterval) :
    ((classify I).upper = true ↔ ∃ x, I.Contains x ∧ f x = true) ∧
    ((classify I).lower = true ↔ ∀ x, I.Contains x → f x = true) := by
  constructor
  · rw [optimistic_iff, exactImage]; rfl
  · rw [pessimistic_iff, exactImage]
    exact ⟨fun h x hx => h (f x) ⟨x, hx, rfl⟩,
      fun h b ⟨x, hx, hb⟩ => hb ▸ h x hx⟩

/-- Sound at each actual same-input numerical witness; no attainment assertion
for a caller's possibly narrower or externally restricted domain. -/
theorem numeric_compatible {α : Type*} (d : α → QInterval)
    (f : ℝ → Bool) (classify : QInterval → Truth)
    (sound : ∀ I x, I.Contains x → f x ∈ (classify I).values)
    (p : α) (x : ℝ) (hx : (d p).Contains x) :
    (domain (fun p => classify (d p))).Compatible p (f x = true) := by
  rw [domain_compatible]
  simpa using sound (d p) x hx

/-- External input partiality is retained; enclosure is needed only where the
input predicate holds. A total numerical representative does not erase a hole. -/
theorem guarded_numeric_compatible {α : Type*} (d : α → QInterval)
    (f : ℝ → Bool) (classify : QInterval → Truth)
    (sound : ∀ I x, I.Contains x → f x ∈ (classify I).values)
    (G : DomainBounds α) (p : α) (P : Prop) (x : ℝ)
    (hg : G.Compatible p P) (hx : P → (d p).Contains x) :
    (G.inter (domain (fun p => classify (d p)))).Compatible p (P ∧ f x = true) := by
  constructor
  · intro h
    have hp := hg.1 h.1
    exact ⟨hp, (numeric_compatible d f classify sound p x (hx hp)).1 h.2⟩
  · rintro ⟨hp, hf⟩
    exact ⟨hg.2 hp, (numeric_compatible d f classify sound p x (hx hp)).2 hf⟩

/-- Numeric widening preserves classification when the classifier describes
all admitted values. It need not preserve the exact classification label. -/
theorem numeric_domain_refines {α : Type*} (d e : α → QInterval)
    (f : ℝ → Bool) (classify : QInterval → Truth)
    (exactImage : ∀ I, (classify I).values = numericImage f I)
    (h : ∀ p x, (d p).Contains x → (e p).Contains x) :
    Refines (domain (fun p => classify (d p))) (domain (fun p => classify (e p))) :=
  domain_refines (fun p => numeric_refines f classify exactImage (h p))

def point (q : ℚ) : QInterval := ⟨q, q, le_rfl⟩
def above (q : ℚ) (I : QInterval) : Truth := StrictComparison.compare (point q) I
def atLeast (q : ℚ) (I : QInterval) : Truth := compareLE (point q) I

noncomputable def gtPredicate (q : ℚ) (x : ℝ) : Bool := by
  classical
  exact decide ((q : ℝ) < x)
noncomputable def gePredicate (q : ℚ) (x : ℝ) : Bool := by
  classical
  exact decide ((q : ℝ) ≤ x)

theorem above_exact (q : ℚ) (I : QInterval) :
    (above q I).values = numericImage (gtPredicate q) I := by
  rw [above, compare_exact]
  ext b
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    have he : x = (q : ℝ) := le_antisymm hx.2 hx.1
    subst x
    exact ⟨y, hy, h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨q, y, ⟨le_rfl, le_rfl⟩, hy, h⟩

theorem atLeast_exact (q : ℚ) (I : QInterval) :
    (atLeast q I).values = numericImage (gePredicate q) I := by
  rw [atLeast, compareLE_exact]
  ext b
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    have he : x = (q : ℝ) := le_antisymm hx.2 hx.1
    subst x
    exact ⟨y, hy, h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨q, y, ⟨le_rfl, le_rfl⟩, hy, h⟩

theorem threshold_compatible {α : Type*} (d : α → QInterval) (q : ℚ)
    (p : α) (x : ℝ) (hx : (d p).Contains x) :
    (domain (fun p => above q (d p))).Compatible p ((q : ℝ) < x) ∧
    (domain (fun p => atLeast q (d p))).Compatible p ((q : ℝ) ≤ x) := by
  classical
  constructor
  · have h := numeric_compatible d (gtPredicate q) (above q)
      (fun I x hx => by rw [above_exact]; exact ⟨x, hx, rfl⟩) p x hx
    simpa [gtPredicate] using h
  · have h := numeric_compatible d (gePredicate q) (atLeast q)
      (fun I x hx => by rw [atLeast_exact]; exact ⟨x, hx, rfl⟩) p x hx
    simpa [gePredicate] using h

/-- Concrete existing partial square-root relation, with the external input
predicate still required. This proves domain compatibility, not a range bound. -/
theorem sqrt_constraint_compatible {α W : Type*} (d : α → QInterval)
    (G : DomainBounds α) (p : α) (w : W) (P : Prop) (x : ℝ)
    (hg : G.Compatible p P) (hx : P → (d p).Contains x) :
    (G.inter (domain (fun p => atLeast 0 (d p)))).Compatible p
      (∃ z, SqrtValues (fun (_ : α) (_ : W) y => P ∧ y = x) p w z) := by
  have h := guarded_numeric_compatible d (gePredicate 0) (atLeast 0)
    (fun I x hx => by rw [atLeast_exact]; exact ⟨x, hx, rfl⟩) G p P x hg hx
  have he : (∃ z, SqrtValues (fun (_ : α) (_ : W) y => P ∧ y = x) p w z) ↔
      P ∧ gePredicate 0 x = true := by
    classical
    simp [SqrtValues, gePredicate, and_assoc]
  exact ⟨fun hd => he.mpr (h.1 hd), fun hz => h.2 (he.mp hz)⟩

end GeneralizedIntervalArithmetic.DomainProjections
