import SquareRootDomains
import AuditPolicy

namespace GeneralizedIntervalArithmetic.SquareRootChecks

def range (a b : ℝ) : PartialEnclosure Unit :=
  ⟨⟨fun _ => a,fun _ => b⟩,⟨fun _ => True,fun _ => True,fun _ h => h⟩⟩
def admitted (a b : ℝ) (_ : Unit) (w : ℝ) : Prop := a ≤ w ∧ w ≤ b
def inputValue (_ : Unit) (w z : ℝ) : Prop := z = w

theorem range_sound (a b : ℝ) : (range a b).UniversalSound (admitted a b) inputValue := by
  intro p w hw
  exact ⟨fun z hz => hz ▸ hw,fun _ => ⟨w,rfl⟩,fun _ => trivial⟩

theorem negative_case :
    (range (-2) (-1)).sqrt.values.lower () = -2 ∧
    (range (-2) (-1)).sqrt.values.upper () = -1 ∧
    ¬ (range (-2) (-1)).sqrt.domain.possible () := by
  norm_num [range,PartialEnclosure.sqrt]

theorem negative_no_roots :
    ¬ ∃ w z, admitted (-2) (-1) () w ∧ SqrtValues inputValue () w z :=
  sqrt_negative_absent (range_sound (-2) (-1)) (by norm_num [range])

theorem mixed_case :
    (range (-1) 1).sqrt.values.lower () = 0 ∧
    (range (-1) 1).sqrt.values.upper () = 1 ∧
    ¬ (range (-1) 1).sqrt.domain.definite () ∧
    (range (-1) 1).sqrt.domain.possible () := by
  norm_num [range,PartialEnclosure.sqrt]

theorem nonnegative_case :
    (range 0 4).sqrt.values.lower () = 0 ∧
    (range 0 4).sqrt.values.upper () = 2 ∧
    (range 0 4).sqrt.domain.definite () := by
  norm_num [range,PartialEnclosure.sqrt,Real.sqrt_eq_cases]

theorem partial_meaning (w : ℝ) :
    (∃ z, SqrtValues inputValue () w z) ↔ 0 ≤ w := by
  rw [sqrt_values_defined_iff]
  simp [inputValue]

/-- Totalized sqrt(-1)=0 cannot create a value of the partial operation. -/
theorem totalization_control : Real.sqrt (-1) = 0 ∧
    ¬ ∃ z, SqrtValues inputValue () (-1) z := by
  constructor
  · exact Real.sqrt_eq_zero_of_nonpos (by norm_num)
  · rw [partial_meaning]; norm_num

/-- The zero boundary remains defined even though its surrounding range is mixed. -/
theorem zero_boundary : (range (-1) 0).sqrt.domain.possible () ∧
    ¬ (range (-1) 0).sqrt.domain.definite () ∧ SqrtValues inputValue () 0 0 := by
  refine ⟨by norm_num [range,PartialEnclosure.sqrt],
    by norm_num [range,PartialEnclosure.sqrt],0,rfl,le_refl _,?_⟩
  simp

theorem nested_roots : ((range 0 4).sqrt.sqrt).UniversalSound (admitted 0 4)
    (SqrtValues (SqrtValues inputValue)) :=
  sqrt_universal_sound (sqrt_universal_sound (range_sound 0 4))

theorem same_input_sum : ((range 0 4).sqrt.add (range 0 4).sqrt).UniversalSound
    (admitted 0 4) (fun p w z => ∃ x y,
      SqrtValues inputValue p w x ∧ SqrtValues inputValue p w y ∧ z = x+y) :=
  universal_add_sound (sqrt_universal_sound (range_sound 0 4))
    (sqrt_universal_sound (range_sound 0 4))

/-- Conservatism: loose input bounds need not certify actual totality. -/
theorem uncertain_despite_single_input :
    (range (-1) 1).UniversalSound (fun _ w => w = (0:ℝ)) inputValue ∧
    (∀ w : ℝ, w = 0 → ∃ z, SqrtValues inputValue () w z) ∧
    ¬ (range (-1) 1).sqrt.domain.definite () := by
  refine ⟨?_,?_,by norm_num [range,PartialEnclosure.sqrt]⟩
  · intro p w hw
    subst w
    exact ⟨fun z hz => by subst z; constructor <;> norm_num [range],
      fun _ => ⟨0,rfl⟩,fun _ => trivial⟩
  · intro w hw
    rw [partial_meaning,hw]

/-- A source-independent external hole remains absent after square root. -/
theorem external_hole :
    ((range 0 4).restrict (fun _ => False)).sqrt.UniversalSound (admitted 0 4)
      (SqrtValues (fun p w z => False ∧ inputValue p w z)) ∧
    ¬ ((range 0 4).restrict (fun _ => False)).sqrt.domain.possible () := by
  exact ⟨sqrt_universal_sound (universal_restrict_sound (range_sound 0 4) (fun _ => False)),
    fun h => h.1.1⟩

/-- Integration with an existing successful guarded interpretation, preserving
its coordinate evidence and external domain rather than asserting totality. -/
theorem guarded_then_sqrt {X Y V : LinearInterval} {e : Expr}
    (E : ℝ → Prop) (A : ℝ → (ℝ × ℝ) → Prop)
    (hx : ∀ t w, A t w → E t → t ∈ Set.Icc (0:ℝ) 1 → X.Contains t w.1)
    (hy : ∀ t w, A t w → E t → t ∈ Set.Icc (0:ℝ) 1 → Y.Contains t w.2)
    (hr : evalGuarded X Y e = some V) :
    (V.partial.restrict E).sqrt.UniversalSound A
      (SqrtValues (fun t w z => E t ∧ t ∈ Set.Icc (0:ℝ) 1 ∧ Value w.1 w.2 e z)) :=
  sqrt_universal_sound (evalGuarded_universal_sound E A hx hy hr)

end GeneralizedIntervalArithmetic.SquareRootChecks
#audit_namespace GeneralizedIntervalArithmetic.SquareRootChecks
