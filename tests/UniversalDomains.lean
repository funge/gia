import UniversalDomains
import ExpressionContinuity
import AuditPolicy

namespace GeneralizedIntervalArithmetic.UniversalDomainChecks

def admitted (_ : Unit) (_ : Bool) : Prop := True
def reciprocal : Expr := .div (.const 1) .x
def inputs (w : Bool) : ℝ := if w then 1 else 0
def meaning (_ : Unit) (w : Bool) (z : ℝ) : Prop := Value (inputs w) 0 reciprocal z

theorem pole_undefined : ¬ ∃ z, meaning () false z := by
  rintro ⟨z,h⟩
  cases h with
  | div ha hb hn => cases hb; exact hn rfl

theorem one_defined : meaning () true 1 := by
  have hc : Value (1:ℝ) 0 (.const 1) 1 := by simpa using (Value.const (1:ℚ) : Value (1:ℝ) 0 (.const 1) (1:ℚ))
  have h : Value (1:ℝ) 0 (.div (.const 1) .x) (1/1) :=
    Value.div hc Value.x (by norm_num)
  simpa [meaning,inputs,reciprocal] using h

def weak : PartialEnclosure Unit :=
  ⟨⟨fun _ => 1, fun _ => 1⟩,⟨fun _ => True,fun _ => True,fun _ h => h⟩⟩

/-- The old contract is satisfied by one successful represented input. -/
theorem existential_sound : weak.Sound (fun p z => ∃ w, admitted p w ∧ meaning p w z) := by
  refine ⟨?_,fun _ _ _ => trivial,fun _ _ => ⟨1,true,trivial,one_defined⟩⟩
  rintro p z ⟨w,_,h⟩
  cases p
  cases w with
  | false => exact False.elim (pole_undefined ⟨z,h⟩)
  | true =>
    have hv := value_eq_realValue h
    norm_num [inputs,reciprocal,Expr.realValue] at hv
    subst z
    exact ⟨le_refl _,le_refl _⟩

theorem existential_not_universal : ¬ weak.UniversalSound admitted meaning := by
  intro h
  exact pole_undefined ((h () false trivial).2.1 trivial)

theorem mixed_exact_domain :
    ¬ (exactInputDomain admitted meaning).definite () ∧
    (exactInputDomain admitted meaning).possible () := by
  exact ⟨fun h => pole_undefined (h.2 false trivial),⟨true,1,trivial,one_defined⟩⟩

def corrected : PartialEnclosure Unit := ⟨weak.values,exactInputDomain admitted meaning⟩

theorem exact_envelope_valid : corrected.UniversalSound admitted meaning := by
  apply exact_input_universal
  intro p w hw z hz
  exact existential_sound.1 p z ⟨w,hw,hz⟩

theorem shared_sum_valid : (corrected.add corrected).UniversalSound admitted
    (fun p w z => ∃ x y, meaning p w x ∧ meaning p w y ∧ z = x+y) :=
  universal_add_sound exact_envelope_valid exact_envelope_valid

def unknownDomain : DomainBounds Unit := ⟨fun _ => False,fun _ => True,fun _ h => h.elim⟩

theorem unknown_allows_both : unknownDomain.Compatible () True ∧
    unknownDomain.Compatible () False := by
  constructor <;> constructor <;> simp [unknownDomain]

/-- Nonempty represented inputs are necessary when projecting universal claims. -/
theorem empty_vacuity : weak.UniversalSound (fun _ (_ : Bool) => False) meaning ∧
    ¬ weak.Sound (fun p z => ∃ w : Bool, False ∧ meaning p w z) := by
  constructor
  · intro _ _ h; exact h.elim
  · intro h
    obtain ⟨_,_,hf,_⟩ := h.2.2 () trivial
    exact hf

theorem exact_empty_not_definite :
    ¬ (exactInputDomain (fun _ (_ : Bool) => False) meaning).definite () := by
  rintro ⟨⟨_,h⟩,_⟩; exact h

def leftValue (_ : Unit) (w : Bool) (z : ℝ) : Prop := w = true ∧ z = 0
def rightValue (_ : Unit) (w : Bool) (z : ℝ) : Prop := w = false ∧ z = 0

theorem separate_witness_control :
    (∃ w z, leftValue () w z) ∧ (∃ w z, rightValue () w z) ∧
    ¬ ∃ w x y, leftValue () w x ∧ rightValue () w y := by
  refine ⟨⟨true,0,rfl,rfl⟩,⟨false,0,rfl,rfl⟩,?_⟩
  rintro ⟨w,x,y,hl,hr⟩
  exact Bool.noConfusion (hl.1.symm.trans hr.1)

def X : LinearInterval := .constant ⟨1,2,by norm_num⟩
def Y : LinearInterval := .constant (.point 0)
def safeX : X.hull.AwayZero := by decide +kernel
def output : LinearInterval := (LinearInterval.exact ⟨1,1⟩).mul (.constant (X.hull.recip safeX))
def coordinates (_ : ℝ) (w : ℝ × ℝ) : Prop := 1 ≤ w.1 ∧ w.1 ≤ 2 ∧ w.2 = 0
def external (t : ℝ) : Prop := t ≠ 1/2

theorem computed_reciprocal : evalGuarded X Y reciprocal = some output := by
  change (LinearInterval.exact ⟨1,1⟩).div? X = some output
  simp [LinearInterval.div?,LinearInterval.recip?,safeX,output]

theorem guarded_all_inputs : (output.partial.restrict external).UniversalSound coordinates
    (fun t w z => external t ∧ t ∈ Set.Icc (0:ℝ) 1 ∧ Value w.1 w.2 reciprocal z) := by
  apply evalGuarded_universal_sound external coordinates _ _ computed_reciprocal
  · intro t w hw _ _
    rw [X,linear_constant_contains]
    simpa [QInterval.Contains] using (And.intro hw.1 hw.2.1)
  · intro t w hw _ _
    rw [Y,linear_constant_contains]
    simp [QInterval.Contains,QInterval.point,hw.2.2]

theorem all_inputs_project : (output.partial.restrict external).Sound
    (fun t z => ∃ w, coordinates t w ∧ external t ∧
      t ∈ Set.Icc (0:ℝ) 1 ∧ Value w.1 w.2 reciprocal z) := by
  apply universal_projects guarded_all_inputs
  intro t _
  exact ⟨(1,0),by norm_num [coordinates]⟩

theorem hole_retained :
    ¬ ∃ (w : ℝ × ℝ) (z : ℝ), external (1/2) ∧ (1/2:ℝ) ∈ Set.Icc 0 1 ∧ Value w.1 w.2 reciprocal z := by
  rintro ⟨w,z,h,_,_⟩
  exact h rfl

end GeneralizedIntervalArithmetic.UniversalDomainChecks
#audit_namespace GeneralizedIntervalArithmetic.UniversalDomainChecks
