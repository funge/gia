import DomainQueries
import ExpressionContinuity

namespace GeneralizedIntervalArithmetic

/-- Small guard fragment over one shared two-coordinate environment. -/
structure RationalAffineForm where
  xCoeff : ℚ
  yCoeff : ℚ
  constant : ℚ
  deriving DecidableEq, Repr

def RationalAffineForm.valueRat (a : RationalAffineForm) (p : ℚ × ℚ) : ℚ :=
  a.xCoeff * p.1 + a.yCoeff * p.2 + a.constant
noncomputable def RationalAffineForm.value (a : RationalAffineForm) (p : ℝ × ℝ) : ℝ :=
  a.xCoeff * p.1 + a.yCoeff * p.2 + a.constant

theorem affine_form_cast (a : RationalAffineForm) (p : ℚ × ℚ) :
    (a.valueRat p : ℝ) = a.value ((p.1:ℝ), (p.2:ℝ)) := by
  simp [RationalAffineForm.valueRat, RationalAffineForm.value]

def RationalAffineForm.expression (a : RationalAffineForm) : Expr :=
  .add (.add (.mul (.const a.xCoeff) .x) (.mul (.const a.yCoeff) .y)) (.const a.constant)

theorem affine_form_value (a : RationalAffineForm) (p : ℝ × ℝ) :
    Value p.1 p.2 a.expression (a.value p) :=
  Value.add (Value.add (Value.mul (Value.const _) Value.x)
    (Value.mul (Value.const _) Value.y)) (Value.const _)

theorem affine_form_unique {a : RationalAffineForm} {p : ℝ × ℝ} {z : ℝ}
    (hz : Value p.1 p.2 a.expression z) : z = a.value p :=
  (value_eq_realValue hz).trans (value_eq_realValue (affine_form_value a p)).symm

/-- Generates existing Expr syntax; it is not a replacement evaluator.
The empty list denotes zero; each denominator contributes its own guard. -/
def affineReciprocalSum : List RationalAffineForm → Expr
  | [] => .const 0
  | a :: rest => .add (.div (.const 1) a.expression) (affineReciprocalSum rest)

/-- Exact partial-domain equivalence at a common real environment. No finite
range, rational-coordinate, or continuity premise is required. -/
theorem affine_sum_defined_iff (gs : List RationalAffineForm) (p : ℝ × ℝ) :
    (∃ z, Value p.1 p.2 (affineReciprocalSum gs) z) ↔
      ∀ a ∈ gs, a.value p ≠ 0 := by
  induction gs with
  | nil => simp only [affineReciprocalSum, List.not_mem_nil, false_implies, implies_true, iff_true]
           exact ⟨0, by simpa using (Value.const (x := p.1) (y := p.2) 0)⟩
  | cons a gs ih =>
    constructor
    · rintro ⟨z, hv⟩
      cases hv with
      | add hl hr =>
        have hg := ih.mp ⟨_, hr⟩
        cases hl with
        | div hn hd hne =>
          have he := affine_form_unique hd
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact he ▸ hne
          · exact hg b hb
    · intro hg
      have hn := hg a (by simp)
      obtain ⟨z, hz⟩ := ih.mpr (fun b hb => hg b (List.mem_cons_of_mem _ hb))
      have hv := Value.div (Value.const 1) (affine_form_value a p) hn
      exact ⟨_, Value.add hv hz⟩

/-- Conjoin before projecting: both sublists use exactly the same environment. -/
theorem affine_sum_append_defined (gs hs : List RationalAffineForm) (p : ℝ × ℝ) :
    (∃ z, Value p.1 p.2 (affineReciprocalSum (gs ++ hs)) z) ↔
    (∃ z, Value p.1 p.2 (affineReciprocalSum gs) z) ∧
    (∃ z, Value p.1 p.2 (affineReciprocalSum hs) z) := by
  simp only [affine_sum_defined_iff, List.mem_append, or_imp, forall_and]

def affineGuardsHold (gs : List RationalAffineForm) (p : ℚ × ℚ) : Bool :=
  gs.all (fun a => decide (a.valueRat p ≠ 0))

theorem affine_guards_hold_iff (gs : List RationalAffineForm) (p : ℚ × ℚ) :
    affineGuardsHold gs p = true ↔ ∀ a ∈ gs, a.value ((p.1:ℝ), (p.2:ℝ)) ≠ 0 := by
  simp only [affineGuardsHold, List.all_eq_true, decide_eq_true_eq]
  apply forall_congr'
  intro a
  apply imp_congr_right
  intro _
  rw [← affine_form_cast]
  exact_mod_cast Iff.rfl

/-- Guard membership is exact; any uncertainty still present comes from the
external domain. This says nothing about existential projection over a region. -/
def affineGuardDomain (gs : List RationalAffineForm) (D : DomainBounds (ℚ × ℚ)) :
    DomainBounds (ℚ × ℚ) :=
  D.inter ⟨fun p => affineGuardsHold gs p = true,
    fun p => affineGuardsHold gs p = true, fun _ h => h⟩

instance affineGuardDomain_def_dec (gs : List RationalAffineForm) (D : DomainBounds (ℚ × ℚ))
    (p : ℚ × ℚ) [Decidable (D.definite p)] : Decidable ((affineGuardDomain gs D).definite p) :=
  inferInstanceAs (Decidable (D.definite p ∧ affineGuardsHold gs p = true))
instance affineGuardDomain_poss_dec (gs : List RationalAffineForm) (D : DomainBounds (ℚ × ℚ))
    (p : ℚ × ℚ) [Decidable (D.possible p)] : Decidable ((affineGuardDomain gs D).possible p) :=
  inferInstanceAs (Decidable (D.possible p ∧ affineGuardsHold gs p = true))

theorem affine_guard_domain_possible {D : DomainBounds (ℚ × ℚ)} {E : (ℚ × ℚ) → Prop}
    (hp : ∀ p, E p → D.possible p) (gs : List RationalAffineForm) (p : ℚ × ℚ) (z : ℝ)
    (hz : E p ∧ Value (p.1:ℝ) (p.2:ℝ) (affineReciprocalSum gs) z) :
    (affineGuardDomain gs D).possible p :=
  ⟨hp p hz.1, (affine_guards_hold_iff gs p).mpr
    ((affine_sum_defined_iff gs _).mp ⟨z, hz.2⟩)⟩

theorem affine_guard_domain_definite {D : DomainBounds (ℚ × ℚ)} {E : (ℚ × ℚ) → Prop}
    (hd : ∀ p, D.definite p → E p) (gs : List RationalAffineForm) (p : ℚ × ℚ)
    (hp : (affineGuardDomain gs D).definite p) :
    ∃ z, E p ∧ Value (p.1:ℝ) (p.2:ℝ) (affineReciprocalSum gs) z := by
  obtain ⟨z, hz⟩ := (affine_sum_defined_iff gs _).mpr ((affine_guards_hold_iff gs p).mp hp.2)
  exact ⟨z, hd p hp.1, hz⟩

/-- An affine function of two independent unit parameters is nonnegative
exactly when its four vertex values are nonnegative. -/
theorem affine_square_nonnegative_iff (a b c : ℝ) :
    (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, 0 ≤ a*x+b*y+c) ↔
      0 ≤ c ∧ 0 ≤ a+c ∧ 0 ≤ b+c ∧ 0 ≤ a+b+c := by
  constructor
  · intro h
    have h00 := h 0 (by constructor <;> norm_num) 0 (by constructor <;> norm_num)
    have h10 := h 1 (by constructor <;> norm_num) 0 (by constructor <;> norm_num)
    have h01 := h 0 (by constructor <;> norm_num) 1 (by constructor <;> norm_num)
    have h11 := h 1 (by constructor <;> norm_num) 1 (by constructor <;> norm_num)
    simpa using And.intro h00 (And.intro h10 (And.intro h01 h11))
  · rintro ⟨h00,h10,h01,h11⟩ x hx y hy
    rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
    · have := mul_nonneg ha hx.1
      have := mul_nonneg hb hy.1
      linarith
    · have := mul_nonneg ha hx.1
      have := mul_le_mul_of_nonpos_left hy.2 hb
      linarith
    · have := mul_le_mul_of_nonpos_left hx.2 ha
      have := mul_nonneg hb hy.1
      linarith
    · have := mul_le_mul_of_nonpos_left hx.2 ha
      have := mul_le_mul_of_nonpos_left hy.2 hb
      linarith

/-- Finite-rational M₂ validity: independent parameters require all four corners.
This specializes the source's pointwise non-collapse condition, not its full
extended-real interval number system. -/
theorem affine_form_square_order_iff (l u : RationalAffineForm) :
    (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      l.value (x,y) ≤ u.value (x,y)) ↔
    l.valueRat (0,0) ≤ u.valueRat (0,0) ∧
    l.valueRat (1,0) ≤ u.valueRat (1,0) ∧
    l.valueRat (0,1) ≤ u.valueRat (0,1) ∧
    l.valueRat (1,1) ≤ u.valueRat (1,1) := by
  have h := affine_square_nonnegative_iff
    ((u.xCoeff:ℝ)-l.xCoeff) ((u.yCoeff:ℝ)-l.yCoeff)
    ((u.constant:ℝ)-l.constant)
  have hp : (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      l.value (x,y) ≤ u.value (x,y)) ↔
      (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      0 ≤ ((u.xCoeff:ℝ)-l.xCoeff)*x + ((u.yCoeff:ℝ)-l.yCoeff)*y +
        ((u.constant:ℝ)-l.constant)) := by
    simp only [RationalAffineForm.value]
    constructor <;> intro hh x hx y hy <;> have := hh x hx y hy <;> nlinarith
  rw [hp,h]
  simp only [RationalAffineForm.valueRat, mul_zero, mul_one, add_zero, zero_add]
  norm_cast
  constructor <;> rintro ⟨h0,h1,h2,h3⟩ <;> constructor <;> try linarith
  all_goals constructor <;> try linarith
  all_goals constructor <;> linarith

/-- False means failure of whole-square ordering, never emptiness of the domain. -/
def affineSquareOrdered (l u : RationalAffineForm) : Bool :=
  decide (l.valueRat (0,0) ≤ u.valueRat (0,0) ∧
    l.valueRat (1,0) ≤ u.valueRat (1,0) ∧
    l.valueRat (0,1) ≤ u.valueRat (0,1) ∧
    l.valueRat (1,1) ≤ u.valueRat (1,1))

theorem affine_square_ordered_iff (l u : RationalAffineForm) :
    affineSquareOrdered l u = true ↔
    ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      l.value (x,y) ≤ u.value (x,y) := by
  simp only [affineSquareOrdered,decide_eq_true_eq]
  exact (affine_form_square_order_iff l u).symm

/-- The same test exactly characterizes nonempty fibers of existing functional
bounds throughout the square; no new interval representation is needed. -/
theorem affine_square_fibers_iff (l u : RationalAffineForm) :
    affineSquareOrdered l u = true ↔
    ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      ∃ z, (FunctionalBounds.mk l.value u.value).Contains (x,y) z := by
  rw [affine_square_ordered_iff]
  constructor
  · intro h x hx y hy
    exact ⟨l.value (x,y),le_refl _,h x hx y hy⟩
  · intro h x hx y hy
    obtain ⟨z,hz⟩ := h x hx y hy
    exact hz.1.trans hz.2

end GeneralizedIntervalArithmetic
