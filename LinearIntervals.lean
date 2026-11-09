import IntervalOps
import Mathlib.Tactic.Ring

namespace GeneralizedIntervalArithmetic

/-- Rational affine bound, represented by its values at parameters 0 and 1. -/
structure QAffine where
  atZero : ℚ
  atOne : ℚ
  deriving DecidableEq, Repr

noncomputable def QAffine.value (a : QAffine) (t : ℝ) : ℝ :=
  (1 - t) * a.atZero + t * a.atOne

def QAffine.add (a b : QAffine) : QAffine :=
  ⟨a.atZero + b.atZero, a.atOne + b.atOne⟩
def QAffine.sub (a b : QAffine) : QAffine :=
  ⟨a.atZero - b.atZero, a.atOne - b.atOne⟩

theorem affine_add_value (a b : QAffine) (t : ℝ) :
    (a.add b).value t = a.value t + b.value t := by
  simp [QAffine.add, QAffine.value]; ring

theorem affine_sub_value (a b : QAffine) (t : ℝ) :
    (a.sub b).value t = a.value t - b.value t := by
  simp [QAffine.sub, QAffine.value]; ring

theorem affine_order {a b : QAffine}
    (h0 : a.atZero ≤ b.atZero) (h1 : a.atOne ≤ b.atOne)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : a.value t ≤ b.value t := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast h0) (sub_nonneg.mpr ht.2)
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast h1) ht.1

/-- Non-collapsing on [0,1]; endpoint checks suffice for affine bounds. -/
structure LinearInterval where
  lower : QAffine
  upper : QAffine
  orderedZero : lower.atZero ≤ upper.atZero
  orderedOne : lower.atOne ≤ upper.atOne

def LinearInterval.Contains (I : LinearInterval) (t z : ℝ) : Prop :=
  I.lower.value t ≤ z ∧ z ≤ I.upper.value t

theorem linear_ordered (I : LinearInterval) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    I.lower.value t ≤ I.upper.value t := affine_order I.orderedZero I.orderedOne ht

def LinearInterval.constant (I : QInterval) : LinearInterval :=
  ⟨⟨I.lo, I.lo⟩, ⟨I.hi, I.hi⟩, I.ordered, I.ordered⟩

def LinearInterval.exact (a : QAffine) : LinearInterval := ⟨a, a, le_rfl, le_rfl⟩

def LinearInterval.add (I J : LinearInterval) : LinearInterval :=
  ⟨I.lower.add J.lower, I.upper.add J.upper,
   add_le_add I.orderedZero J.orderedZero, add_le_add I.orderedOne J.orderedOne⟩

def LinearInterval.sub (I J : LinearInterval) : LinearInterval :=
  ⟨I.lower.sub J.upper, I.upper.sub J.lower,
   sub_le_sub I.orderedZero J.orderedZero, sub_le_sub I.orderedOne J.orderedOne⟩

theorem linear_constant_contains (I : QInterval) (t z : ℝ) :
    (LinearInterval.constant I).Contains t z ↔ I.Contains z := by
  have h (q : ℚ) : (1-t)*(q:ℝ)+t*q = q := by ring
  simp [LinearInterval.Contains, LinearInterval.constant, QAffine.value,
    QInterval.Contains, h]

theorem linear_exact_contains (a : QAffine) (t z : ℝ) :
    (LinearInterval.exact a).Contains t z ↔ z = a.value t := by
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => h ▸ ⟨le_rfl, le_rfl⟩⟩

theorem linear_add_encloses {I J : LinearInterval} {t x y : ℝ}
    (hx : I.Contains t x) (hy : J.Contains t y) : (I.add J).Contains t (x+y) := by
  change (I.lower.add J.lower).value t ≤ x+y ∧ x+y ≤ (I.upper.add J.upper).value t
  rw [affine_add_value, affine_add_value]
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem linear_sub_encloses {I J : LinearInterval} {t x y : ℝ}
    (hx : I.Contains t x) (hy : J.Contains t y) : (I.sub J).Contains t (x-y) := by
  change (I.lower.sub J.upper).value t ≤ x-y ∧ x-y ≤ (I.upper.sub J.lower).value t
  rw [affine_sub_value, affine_sub_value]
  exact ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

/-- Forget parameter dependence conservatively. This need not be an optimal hull. -/
def LinearInterval.hull (I : LinearInterval) : QInterval :=
  ⟨min I.lower.atZero I.lower.atOne, max I.upper.atZero I.upper.atOne,
   (min_le_left _ _).trans (I.orderedZero.trans (le_max_left _ _))⟩

theorem linear_hull_encloses {I : LinearInterval} {t z : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hz : I.Contains t z) : I.hull.Contains z := by
  have hl := affine_order (a := ⟨I.hull.lo, I.hull.lo⟩) (b := I.lower)
    (min_le_left _ _) (min_le_right _ _) ht
  have hu := affine_order (a := I.upper) (b := ⟨I.hull.hi, I.hull.hi⟩)
    (le_max_left _ _) (le_max_right _ _) ht
  have h (q : ℚ) : (QAffine.mk q q).value t = q := by simp [QAffine.value]; ring
  rw [h] at hl hu
  exact ⟨hl.trans hz.1, hz.2.trans hu⟩

theorem linear_exact_cancel (a : QAffine) (t z : ℝ) :
    ((LinearInterval.exact a).sub (.exact a)).Contains t z ↔ z = 0 := by
  simp [LinearInterval.Contains, LinearInterval.sub, LinearInterval.exact,
    QAffine.sub, QAffine.value, le_antisymm_iff, and_comm]


/-- Coefficient form a + b*t translated to the existing endpoint representation.
This is the finite-rational fragment of thesis §2.9.3, printed pp.28–29. -/
def QAffine.ofCoefficients (a b : ℚ) : QAffine := ⟨a, a+b⟩

def QAffine.coefficients (q : QAffine) : ℚ × ℚ :=
  (q.atZero, q.atOne-q.atZero)

theorem affine_ofCoefficients_value (a b : ℚ) (t : ℝ) :
    (QAffine.ofCoefficients a b).value t = (a:ℝ) + (b:ℝ)*t := by
  simp [QAffine.ofCoefficients,QAffine.value]
  ring

theorem affine_coefficients_roundtrip (a b : ℚ) :
    (QAffine.ofCoefficients a b).coefficients = (a,b) := by
  simp [QAffine.ofCoefficients,QAffine.coefficients]

theorem affine_endpoints_roundtrip (q : QAffine) :
    QAffine.ofCoefficients q.coefficients.1 q.coefficients.2 = q := by
  cases q
  simp [QAffine.ofCoefficients,QAffine.coefficients]

/-- Endpoint checks are necessary as well as sufficient on the closed unit interval. -/
theorem affine_order_iff (a b : QAffine) :
    (a.atZero ≤ b.atZero ∧ a.atOne ≤ b.atOne) ↔
      ∀ t ∈ Set.Icc (0:ℝ) 1, a.value t ≤ b.value t := by
  constructor
  · rintro ⟨h0,h1⟩ t ht
    exact affine_order h0 h1 ht
  · intro h
    have h0 := h 0 (by norm_num)
    have h1 := h 1 (by norm_num)
    simp only [QAffine.value,sub_zero,one_mul,zero_mul,add_zero] at h0
    simp only [QAffine.value,sub_self,zero_mul,one_mul,zero_add] at h1
    exact ⟨by exact_mod_cast h0,by exact_mod_cast h1⟩

/-- Precisely the non-collapsing condition for finite rational coefficient bounds. -/
theorem affine_coefficients_order_iff (a b c d : ℚ) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, (a:ℝ)+(b:ℝ)*t ≤ (c:ℝ)+(d:ℝ)*t) ↔
      a ≤ c ∧ a+b ≤ c+d := by
  simpa only [affine_ofCoefficients_value] using
    (affine_order_iff (QAffine.ofCoefficients a b) (QAffine.ofCoefficients c d)).symm

/-- Every ordered coefficient description is representable, and only those are.
No extended-real coefficients or numerical rounding model is introduced. -/
theorem linear_coefficients_realizable_iff (a b c d : ℚ) :
    (∃ I : LinearInterval, I.lower = QAffine.ofCoefficients a b ∧
      I.upper = QAffine.ofCoefficients c d) ↔
      ∀ t ∈ Set.Icc (0:ℝ) 1, (a:ℝ)+(b:ℝ)*t ≤ (c:ℝ)+(d:ℝ)*t := by
  constructor
  · rintro ⟨I,hl,hu⟩ t ht
    have h := linear_ordered I ht
    rw [hl,hu,affine_ofCoefficients_value,affine_ofCoefficients_value] at h
    exact h
  · intro h
    have hh := (affine_coefficients_order_iff a b c d).mp h
    exact ⟨⟨QAffine.ofCoefficients a b,QAffine.ofCoefficients c d,hh.1,hh.2⟩,rfl,rfl⟩

/-- The source coefficient inequalities give exactly the existing containment
predicate, for every real parameter, without asserting ordering outside [0,1]. -/
theorem linear_coefficients_contains (I : LinearInterval) (t z : ℝ) :
    I.Contains t z ↔
      (I.lower.coefficients.1:ℝ) + (I.lower.coefficients.2:ℝ)*t ≤ z ∧
      z ≤ (I.upper.coefficients.1:ℝ) + (I.upper.coefficients.2:ℝ)*t := by
  have hl := affine_ofCoefficients_value I.lower.coefficients.1 I.lower.coefficients.2 t
  have hu := affine_ofCoefficients_value I.upper.coefficients.1 I.upper.coefficients.2 t
  rw [affine_endpoints_roundtrip] at hl hu
  exact by simp only [LinearInterval.Contains,hl,hu]


/-- Thesis §2.9.4's constant embedding, restricted to finite rational endpoints,
has zero slope on both bounds in the coefficient representation. -/
theorem linear_constant_coefficients (I : QInterval) :
    ((LinearInterval.constant I).lower.coefficients,
      (LinearInterval.constant I).upper.coefficients) = ((I.lo,0),(I.hi,0)) := by
  simp [LinearInterval.constant,QAffine.coefficients]

/-- Forgetting parameter dependence is a left inverse on constant intervals. -/
theorem linear_constant_hull (I : QInterval) : (LinearInterval.constant I).hull = I := by
  cases I
  simp [LinearInterval.constant,LinearInterval.hull]

theorem linear_constant_injective : Function.Injective LinearInterval.constant := by
  intro I J h
  have hh := congrArg LinearInterval.hull h
  simpa only [linear_constant_hull] using hh

theorem linear_constant_add (I J : QInterval) :
    (LinearInterval.constant I).add (.constant J) = .constant (I.add J) := rfl

theorem linear_constant_sub (I J : QInterval) :
    (LinearInterval.constant I).sub (.constant J) = .constant (I.sub J) := rfl

end GeneralizedIntervalArithmetic
