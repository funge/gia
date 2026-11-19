import ConditionalArithmetic
import HardwareQuotient
import AuditPolicy

namespace GeneralizedIntervalArithmetic.PartialRealArithmeticChecks
open PartialRealArithmetic

-- Independent legacy definitions pin the original reductions constructor by constructor.
def oldRel : ArithmeticOp → ℝ → ℝ → ℝ → Prop
  | .add, x,y,z => z=x+y
  | .sub, x,y,z => z=x-y
  | .mul, x,y,z => z=x*y
  | .div, x,y,z => y ≠ 0 ∧ z=x/y

noncomputable def oldMeaning : HardwareQuotient.Operation → ℝ → ℝ → ℝ
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .div => (· / ·)

def oldDefined : HardwareQuotient.Operation → ℝ → ℝ → Prop
  | .div, _,y => y ≠ 0
  | _,_,_ => True

def corresponding : ArithmeticOp → HardwareQuotient.Operation
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div

theorem legacy_relation (k : ArithmeticOp) : k.Rel = oldRel k := by cases k <;> rfl
theorem legacy_meaning (k : HardwareQuotient.Operation) : HardwareQuotient.meaning k = oldMeaning k := by cases k <;> rfl
theorem legacy_domain (k : HardwareQuotient.Operation) : HardwareQuotient.Defined k = oldDefined k := by cases k <;> rfl

theorem cross_interface (k : ArithmeticOp) (x y z : ℝ) :
    k.Rel x y z ↔ HardwareQuotient.Defined (corresponding k) x y ∧
      z=HardwareQuotient.meaning (corresponding k) x y := by
  cases k <;> simp [ArithmeticOp.Rel,corresponding,HardwareQuotient.Defined,HardwareQuotient.meaning]

-- Dependent motives exercise the actual public recursors, not replacement aliases.
abbrev AToken : ArithmeticOp → Type
  | .add => Unit | .sub => Bool | .mul => Nat | .div => Int
noncomputable def aToken : (k : ArithmeticOp) → AToken k := ArithmeticOp.rec () true 7 (-2)

abbrev HToken : HardwareQuotient.Operation → Type
  | .add => Unit | .sub => Bool | .mul => Nat | .div => Int
noncomputable def hToken : (k : HardwareQuotient.Operation) → HToken k := HardwareQuotient.Operation.rec () true 7 (-2)

def aPattern : (k : ArithmeticOp) → AToken k
  | .add => () | .sub => true | .mul => 7 | .div => -2

def hPattern : (k : HardwareQuotient.Operation) → HToken k
  | .add => () | .sub => true | .mul => 7 | .div => -2

theorem dependent_pattern_parity :
    (∀ k, aPattern k = aToken k) ∧ (∀ k, hPattern k = hToken k) := by
  constructor <;> intro k <;> cases k <;> rfl

theorem dependent_reductions : aToken .add = () ∧ aToken .sub = true ∧
    aToken .mul = 7 ∧ aToken .div = -2 ∧ hToken .add = () ∧ hToken .sub = true ∧
    hToken .mul = 7 ∧ hToken .div = -2 := by decide

theorem division_domain (x y : ℝ) : (∃ z, ArithmeticOp.div.Rel x y z) ↔ y ≠ 0 := div_domain_iff x y

theorem no_zero_quotient (x z : ℝ) : ¬ ArithmeticOp.div.Rel x 0 z := div_zero x z

theorem negative_denominator : ArithmeticOp.div.Rel 6 (-2) (-3) ∧
    HardwareQuotient.Defined .div 6 (-2) := by norm_num [ArithmeticOp.Rel,HardwareQuotient.Defined,divRel,divDefined,PartialRealArithmetic.div]

theorem quotient_value (x y z : ℝ) :
    HardwareQuotient.Value some 0 (.binary .div (.polynomial (.const x)) (.polynomial (.const y))) z ↔
      divRel x y z := by
  constructor
  · intro h
    cases h with
    | binary hx hy hd =>
      cases hx with
      | polynomial hx =>
        cases hx with
        | const hx =>
          cases hy with
          | polynomial hy =>
            cases hy with
            | const hy =>
              simp only [Option.some.injEq] at hx hy
              subst_vars
              exact ⟨hd,rfl⟩
  · rintro ⟨hy,rfl⟩
    exact .binary (.polynomial (.const rfl)) (.polynomial (.const rfl)) hy

theorem quotient_pole (x : ℝ) : ¬ ∃ z,
    HardwareQuotient.Value some 0 (.binary .div (.polynomial (.const x)) (.polynomial (.const 0))) z := by
  rintro ⟨z,hz⟩
  exact div_zero x z ((quotient_value x 0 z).mp hz)

theorem quotient_nonzero (x y : ℝ) (hy : y ≠ 0) :
    HardwareQuotient.Value some 0 (.binary .div (.polynomial (.const x)) (.polynomial (.const y))) (x/y) :=
  (quotient_value x y (x/y)).mpr ⟨hy,rfl⟩

#audit_namespace GeneralizedIntervalArithmetic.PartialRealArithmeticChecks
end GeneralizedIntervalArithmetic.PartialRealArithmeticChecks
