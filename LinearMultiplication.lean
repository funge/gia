import PartialEnclosures
import Mathlib.Tactic.Linarith

namespace GeneralizedIntervalArithmetic

/-- Merge affine bounds by their endpoint values, retaining parameter dependence. -/
def LinearInterval.join (I J : LinearInterval) : LinearInterval :=
  ⟨⟨min I.lower.atZero J.lower.atZero, min I.lower.atOne J.lower.atOne⟩,
   ⟨max I.upper.atZero J.upper.atZero, max I.upper.atOne J.upper.atOne⟩,
   (min_le_left _ _).trans (I.orderedZero.trans (le_max_left _ _)),
   (min_le_left _ _).trans (I.orderedOne.trans (le_max_left _ _))⟩

theorem linear_join_left {I J : LinearInterval} {t z : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hz : I.Contains t z) : (I.join J).Contains t z :=
  ⟨(affine_order (min_le_left _ _) (min_le_left _ _) ht).trans hz.1,
   hz.2.trans (affine_order (le_max_left _ _) (le_max_left _ _) ht)⟩

theorem linear_join_right {I J : LinearInterval} {t z : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hz : J.Contains t z) : (I.join J).Contains t z :=
  ⟨(affine_order (min_le_right _ _) (min_le_right _ _) ht).trans hz.1,
   hz.2.trans (affine_order (le_max_right _ _) (le_max_right _ _) ht)⟩

def QAffine.curvature (a b : QAffine) : ℚ :=
  (a.atOne - a.atZero) * (b.atOne - b.atZero)

def QAffine.productChord (a b : QAffine) : QAffine :=
  ⟨a.atZero*b.atZero, a.atOne*b.atOne⟩

theorem affine_product_identity (a b : QAffine) (t : ℝ) :
    a.value t * b.value t = (a.productChord b).value t -
      (a.curvature b : ℝ) * (t*(1-t)) := by
  simp [QAffine.value, QAffine.curvature, QAffine.productChord]
  ring

theorem parameter_bubble_bounds {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ t*(1-t) ∧ t*(1-t) ≤ 1/4 := by
  constructor
  · exact mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  · nlinarith [sq_nonneg (t - 1/2)]

/-- The product is quadratic. Shift its endpoint chord by a certified one-sided
curvature error, never treating the endpoint chord alone as an enclosure. -/
def QAffine.productBounds (a b : QAffine) : LinearInterval :=
  ⟨⟨a.atZero*b.atZero - max (a.curvature b) 0 / 4,
     a.atOne*b.atOne - max (a.curvature b) 0 / 4⟩,
   ⟨a.atZero*b.atZero - min (a.curvature b) 0 / 4,
     a.atOne*b.atOne - min (a.curvature b) 0 / 4⟩,
   sub_le_sub_left (div_le_div_of_nonneg_right
     ((min_le_left _ _).trans (le_max_left _ _)) (by norm_num)) _,
   sub_le_sub_left (div_le_div_of_nonneg_right
     ((min_le_left _ _).trans (le_max_left _ _)) (by norm_num)) _⟩

theorem affine_product_encloses (a b : QAffine) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (a.productBounds b).Contains t (a.value t * b.value t) := by
  obtain ⟨h0, h1⟩ := parameter_bubble_bounds ht
  rw [affine_product_identity]
  have hmax : (a.curvature b : ℝ) * (t*(1-t)) ≤ max (a.curvature b : ℝ) 0 / 4 := by
    rcases le_total 0 (a.curvature b : ℝ) with hp | hn
    · rw [max_eq_left hp]
      have := mul_le_mul_of_nonneg_left h1 hp
      nlinarith
    · rw [max_eq_right hn]
      exact le_trans (mul_nonpos_of_nonpos_of_nonneg hn h0) (by norm_num)
  have hmin : min (a.curvature b : ℝ) 0 / 4 ≤ (a.curvature b : ℝ) * (t*(1-t)) := by
    rcases le_total 0 (a.curvature b : ℝ) with hp | hn
    · rw [min_eq_right hp]
      exact le_trans (by norm_num) (mul_nonneg hp h0)
    · rw [min_eq_left hn]
      have := mul_le_mul_of_nonpos_left h1 hn
      nlinarith
  change _ ≤ _ ∧ _ ≤ _
  simp only [QAffine.productBounds, QAffine.value, QAffine.productChord,
    Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_max, Rat.cast_min,
    Rat.cast_zero, Rat.cast_ofNat]
  constructor <;> nlinarith

private theorem real_mul_between {a b x : ℝ} (hx : a ≤ x ∧ x ≤ b) (y : ℝ) :
    min (a*y) (b*y) ≤ x*y ∧ x*y ≤ max (a*y) (b*y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hy),
      (mul_le_mul_of_nonneg_right hx.2 hy).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hy),
      (mul_le_mul_of_nonpos_right hx.1 hy).trans (le_max_left _ _)⟩

/-- Four corner products suffice without sign assumptions on the operands. -/
theorem real_product_bounds {a b c d x y l u : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hac : l ≤ a*c ∧ a*c ≤ u) (had : l ≤ a*d ∧ a*d ≤ u)
    (hbc : l ≤ b*c ∧ b*c ≤ u) (hbd : l ≤ b*d ∧ b*d ≤ u) :
    l ≤ x*y ∧ x*y ≤ u := by
  have ha := real_mul_between hy a
  have hb := real_mul_between hy b
  simp only [mul_comm] at ha hb
  have hxy := real_mul_between hx y
  have ha' : l ≤ a*y ∧ a*y ≤ u :=
    ⟨(le_min hac.1 had.1).trans ha.1, ha.2.trans (max_le hac.2 had.2)⟩
  have hb' : l ≤ b*y ∧ b*y ≤ u :=
    ⟨(le_min hbc.1 hbd.1).trans hb.1, hb.2.trans (max_le hbc.2 hbd.2)⟩
  exact ⟨(le_min ha'.1 hb'.1).trans hxy.1, hxy.2.trans (max_le ha'.2 hb'.2)⟩

def LinearInterval.mul (I J : LinearInterval) : LinearInterval :=
  ((I.lower.productBounds J.lower).join (I.lower.productBounds J.upper)).join
    ((I.upper.productBounds J.lower).join (I.upper.productBounds J.upper))

theorem linear_mul_encloses {I J : LinearInterval} {t x y : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : I.Contains t x) (hy : J.Contains t y) :
    (I.mul J).Contains t (x*y) := by
  apply real_product_bounds hx hy
  · exact linear_join_left ht (linear_join_left ht (affine_product_encloses _ _ ht))
  · exact linear_join_left ht (linear_join_right ht (affine_product_encloses _ _ ht))
  · exact linear_join_right ht (linear_join_left ht (affine_product_encloses _ _ ht))
  · exact linear_join_right ht (linear_join_right ht (affine_product_encloses _ _ ht))

def DomainBounds.inter {α : Type*} (D E : DomainBounds α) : DomainBounds α :=
  ⟨fun p => D.definite p ∧ E.definite p, fun p => D.possible p ∧ E.possible p,
   fun p h => ⟨D.consistent p h.1, E.consistent p h.2⟩⟩

/-- A linear value bound with explicit domain information, restricted to its
certified parameter range. This does not assert definite domain membership. -/
noncomputable def LinearInterval.onDomain (I : LinearInterval) (D : DomainBounds ℝ) :
    PartialEnclosure ℝ :=
  ⟨⟨I.lower.value, I.upper.value⟩,
   ⟨fun t => t ∈ Set.Icc (0:ℝ) 1 ∧ D.definite t,
    fun t => t ∈ Set.Icc (0:ℝ) 1 ∧ D.possible t,
    fun t h => ⟨h.1, D.consistent t h.2⟩⟩⟩

def ProductValues {α : Type*} (R S : α → ℝ → Prop) (p : α) (z : ℝ) : Prop :=
  ∃ x y, R p x ∧ S p y ∧ z = x*y

theorem linear_mul_domain_sound {I J : LinearInterval} {D E : DomainBounds ℝ}
    {R S : ℝ → ℝ → Prop} (hI : (I.onDomain D).Sound R)
    (hJ : (J.onDomain E).Sound S) :
    ((I.mul J).onDomain (D.inter E)).Sound (ProductValues R S) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro t z ⟨x, y, hx, hy, rfl⟩
    exact linear_mul_encloses (hI.2.1 t x hx).1 (hI.1 t x hx) (hJ.1 t y hy)
  · rintro t z ⟨x, y, hx, hy, _⟩
    exact ⟨(hI.2.1 t x hx).1, (hI.2.1 t x hx).2, (hJ.2.1 t y hy).2⟩
  · intro t ht
    obtain ⟨x, hx⟩ := hI.2.2 t ⟨ht.1, ht.2.1⟩
    obtain ⟨y, hy⟩ := hJ.2.2 t ⟨ht.1, ht.2.2⟩
    exact ⟨x*y, x, y, hx, hy, rfl⟩


/-- The chosen four-corner linear multiplication agrees exactly with ordinary
interval multiplication on the constant-image fragment; curvature vanishes. -/
theorem linear_constant_mul (I J : QInterval) :
    (LinearInterval.constant I).mul (.constant J) = .constant (I.mul J) := by
  simp [LinearInterval.mul,LinearInterval.constant,LinearInterval.join,
    QAffine.productBounds,QAffine.curvature,QInterval.mul]

/-- Coefficient form of the existing exact affine-product identity. -/
theorem affine_product_quadratic (a b c d : ℚ) (t : ℝ) :
    (QAffine.ofCoefficients a b).value t * (QAffine.ofCoefficients c d).value t =
      (a:ℝ)*c + ((a:ℝ)*d + (b:ℝ)*c)*t + (b:ℝ)*d*t^2 := by
  rw [affine_ofCoefficients_value, affine_ofCoefficients_value]
  ring

/-- Exact chord residual for a finite real quadratic; no domain restrictions. -/
theorem quadratic_chord_identity (p q r t : ℝ) :
    p + q*t + r*t^2 = (1-t)*p + t*(p+q+r) - r*(t*(1-t)) := by ring

/-- Smallest downward constant shift of this fixed chord, not of arbitrary
slope-changing affine bounds. Endpoint and midpoint witnesses prove necessity. -/
theorem quadratic_chord_lower_iff (p q r δ : ℝ) :
    (∀ t ∈ Set.Icc (0:ℝ) 1,
      (1-t)*p + t*(p+q+r) - δ ≤ p+q*t+r*t^2) ↔ max r 0 / 4 ≤ δ := by
  constructor
  · intro h
    have h0 := h 0 (by constructor <;> norm_num)
    have hm := h (1/2) (by constructor <;> norm_num)
    rcases le_total 0 r with hr | hr
    · rw [max_eq_left hr]; nlinarith
    · rw [max_eq_right hr]; nlinarith
  · intro h t ht
    rw [quadratic_chord_identity]
    obtain ⟨h0,h1⟩ := parameter_bubble_bounds ht
    rcases le_total 0 r with hr | hr
    · rw [max_eq_left hr] at h
      have := mul_le_mul_of_nonneg_left h1 hr
      linarith
    · rw [max_eq_right hr] at h
      have := mul_nonpos_of_nonpos_of_nonneg hr h0
      linarith

/-- Largest upward-side chord subtraction; negative δ denotes an upward shift. -/
theorem quadratic_chord_upper_iff (p q r δ : ℝ) :
    (∀ t ∈ Set.Icc (0:ℝ) 1,
      p+q*t+r*t^2 ≤ (1-t)*p + t*(p+q+r) - δ) ↔ δ ≤ min r 0 / 4 := by
  constructor
  · intro h
    have h0 := h 0 (by constructor <;> norm_num)
    have hm := h (1/2) (by constructor <;> norm_num)
    rcases le_total 0 r with hr | hr
    · rw [min_eq_right hr]; nlinarith
    · rw [min_eq_left hr]; nlinarith
  · intro h t ht
    rw [quadratic_chord_identity]
    obtain ⟨h0,h1⟩ := parameter_bubble_bounds ht
    rcases le_total 0 r with hr | hr
    · rw [min_eq_right hr] at h
      have := mul_nonneg hr h0
      linarith
    · rw [min_eq_left hr] at h
      have := mul_le_mul_of_nonpos_left h1 hr
      linarith

end GeneralizedIntervalArithmetic
