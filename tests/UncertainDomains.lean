import DomainEvaluator
import GuardedEvaluator
import FiniteLinearCovers
import AuditPolicy

namespace GeneralizedIntervalArithmetic.UncertainDomainChecks

def Input (x : ℝ) : Prop := x = -1 ∨ x = 1
def left : Expr := .div (.const 1) (.sub .x (.const 1))
def right : Expr := .div (.const 1) (.add .x (.const 1))
def combined : Expr := .add left right

def LeftValues (_ : Unit) (z : ℝ) := ∃ x, Input x ∧ Value x 0 left z
def RightValues (_ : Unit) (z : ℝ) := ∃ x, Input x ∧ Value x 0 right z

theorem left_at_minus_one : Value (-1) 0 left (-1/2) := by
  have hb := Value.sub (x := (-1:ℝ)) (y := (0:ℝ)) Value.x (Value.const 1)
  norm_num at hb
  have hv := Value.div (Value.const 1) hb (by norm_num)
  simpa [left, div_eq_mul_inv] using hv

theorem right_at_one : Value 1 0 right (1/2) := by
  have hb := Value.add (x := (1:ℝ)) (y := (0:ℝ)) Value.x (Value.const 1)
  norm_num at hb
  have hv := Value.div (Value.const 1) hb (by norm_num)
  simpa [right] using hv

theorem left_at_one_undefined : ¬ ∃ z, Value 1 0 left z := by
  rintro ⟨z, hv⟩
  cases hv with
  | div ha hb hn =>
    cases hb with
    | sub hx hc => cases hx; cases hc; norm_num at hn

theorem right_at_minus_one_undefined : ¬ ∃ z, Value (-1) 0 right z := by
  rintro ⟨z, hv⟩
  cases hv with
  | div ha hb hn =>
    cases hb with
    | add hx hc => cases hx; cases hc; norm_num at hn

theorem left_values_exact (z : ℝ) : LeftValues () z ↔ z = -1/2 := by
  constructor
  · rintro ⟨x, hx, hv⟩
    rcases hx with rfl | rfl
    · cases hv with
      | div ha hb hn =>
        cases ha
        cases hb with
        | sub hx hc => cases hx; cases hc; norm_num
    · exact (left_at_one_undefined ⟨z, hv⟩).elim
  · rintro rfl
    exact ⟨-1, Or.inl rfl, left_at_minus_one⟩

theorem right_values_exact (z : ℝ) : RightValues () z ↔ z = 1/2 := by
  constructor
  · rintro ⟨x, hx, hv⟩
    rcases hx with rfl | rfl
    · exact (right_at_minus_one_undefined ⟨z, hv⟩).elim
    · cases hv with
      | div ha hb hn =>
        cases ha
        cases hb with
        | add hx hc => cases hx; cases hc; norm_num
  · rintro rfl
    exact ⟨1, Or.inr rfl, right_at_one⟩

def totalDomain : DomainBounds Unit := ⟨fun _ => True, fun _ => True, fun _ h => h⟩
noncomputable def leftEnclosure : PartialEnclosure Unit :=
  ⟨⟨fun _ => -1/2, fun _ => -1/2⟩, totalDomain⟩
noncomputable def rightEnclosure : PartialEnclosure Unit :=
  ⟨⟨fun _ => 1/2, fun _ => 1/2⟩, totalDomain⟩

theorem left_sound : leftEnclosure.Sound LeftValues := by
  refine ⟨?_, fun _ _ _ => trivial, ?_⟩
  · rintro ⟨⟩ z hz
    obtain rfl := (left_values_exact z).mp hz
    exact ⟨le_rfl, le_rfl⟩
  · rintro ⟨⟩ _
    exact ⟨-1/2, (left_values_exact _).mpr rfl⟩
theorem right_sound : rightEnclosure.Sound RightValues := by
  refine ⟨?_, fun _ _ _ => trivial, ?_⟩
  · rintro ⟨⟩ z hz
    obtain rfl := (right_values_exact z).mp hz
    exact ⟨le_rfl, le_rfl⟩
  · rintro ⟨⟩ _
    exact ⟨1/2, (right_values_exact _).mpr rfl⟩

-- The existing arithmetic theorem is correct for its independent-witness relation.
theorem independent_sum_sound :
    (leftEnclosure.add rightEnclosure).Sound (SumValues LeftValues RightValues) :=
  partial_add_sound left_sound right_sound

theorem independent_sum_exists : SumValues LeftValues RightValues () 0 :=
  ⟨-1/2, 1/2, (left_values_exact _).mpr rfl, (right_values_exact _).mpr rfl, by norm_num⟩

-- It cannot be reinterpreted as an expression with one shared input.
theorem shared_input_sum_absent : ¬ ∃ x z, Input x ∧ Value x 0 combined z := by
  rintro ⟨x, z, hx, hv⟩
  cases hv with
  | add ha hb =>
    rcases hx with rfl | rfl
    · exact right_at_minus_one_undefined ⟨_, hb⟩
    · exact left_at_one_undefined ⟨_, ha⟩

theorem cannot_reinterpret_independent_sum :
    ¬ (leftEnclosure.add rightEnclosure).Sound
      (fun _ z => ∃ x, Input x ∧ Value x 0 combined z) := by
  intro h
  obtain ⟨z, x, hx, hv⟩ := h.2.2 () ⟨trivial, trivial⟩
  exact shared_input_sum_absent ⟨x, z, hx, hv⟩

theorem children_not_uniform :
    ¬ (∀ x, Input x → ∃ z, Value x 0 left z) ∧
    ¬ (∀ x, Input x → ∃ z, Value x 0 right z) := by
  exact ⟨fun h => left_at_one_undefined (h 1 (Or.inr rfl)),
    fun h => right_at_minus_one_undefined (h (-1) (Or.inl rfl))⟩

-- Uniform child guarantees plus an actual common input do compose safely.
theorem uniform_children_compose (A : ℝ → Prop) (a b : Expr)
    (hA : ∃ x, A x)
    (ha : ∀ x, A x → ∃ u, Value x 0 a u)
    (hb : ∀ x, A x → ∃ v, Value x 0 b v) :
    ∃ x z, A x ∧ Value x 0 (.add a b) z := by
  obtain ⟨x, hx⟩ := hA
  obtain ⟨u, hu⟩ := ha x hx
  obtain ⟨v, hv⟩ := hb x hx
  exact ⟨x, u+v, hx, Value.add hu hv⟩

-- The hull contains a valid arithmetic midpoint, but the external input set does not.
def hull : LinearInterval := .constant ⟨-1, 1, by norm_num⟩
def zero : LinearInterval := .exact ⟨0, 0⟩
theorem inputs_enclosed {x : ℝ} (hx : Input x) : hull.Contains (1/2) x := by
  rw [hull, linear_constant_contains]
  rcases hx with rfl | rfl <;> norm_num [QInterval.Contains]
theorem midpoint_excluded : ¬ Input 0 := by norm_num [Input]
theorem midpoint_arithmetic_defined : Value 0 0 combined 0 := by
  have hlb := Value.sub (x := (0:ℝ)) (y := (0:ℝ)) Value.x (Value.const 1)
  have hrb := Value.add (x := (0:ℝ)) (y := (0:ℝ)) Value.x (Value.const 1)
  norm_num at hlb hrb
  have hl := Value.div (Value.const 1) hlb (by norm_num)
  have hr := Value.div (Value.const 1) hrb (by norm_num)
  have hs := Value.add hl hr
  simpa [combined, left, right] using hs

theorem current_guarded_unknown : (evalGuarded hull zero combined).isNone = true := by
  decide +kernel

-- Finite component unions cannot represent the full reciprocal range of an
-- uncertain input interval crossing zero, even with the zero input excluded.
def PoleRange (t z : ℝ) := t = 0 ∧ ∃ x, x ∈ Set.Icc (-1:ℝ) 1 ∧
  x ≠ 0 ∧ Value x 0 (.div (.const 1) .x) z

theorem pole_range_unbounded (l : ℝ) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, ∃ z, PoleRange t z ∧ z < l := by
  let d := |l| + 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : 1 ≤ d := by dsimp [d]; have := abs_nonneg l; linarith
  have hi : 0 < (1:ℝ)/d := div_pos zero_lt_one hd
  have hi1 : (1:ℝ)/d ≤ 1 := (div_le_iff₀ hd).mpr (by simpa using hd1)
  have hn : -(1/d) ≠ (0:ℝ) := by linarith
  refine ⟨0, by norm_num, -d, ⟨rfl, -(1/d), ⟨by linarith, by linarith⟩, hn, ?_⟩, ?_⟩
  · have hv := Value.div (x := -(1/d)) (y := (0:ℝ)) (Value.const 1) Value.x hn
    simpa [one_div] using hv
  · have hl := neg_abs_le l
    dsimp [d]
    linarith

theorem finite_cover_cannot_fix_pole (C : FiniteLinearCover) : ¬ C.Covers PoleRange :=
  no_finite_cover_of_unbounded_below pole_range_unbounded C

end GeneralizedIntervalArithmetic.UncertainDomainChecks
#audit_namespace GeneralizedIntervalArithmetic.UncertainDomainChecks
