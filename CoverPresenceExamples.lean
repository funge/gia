import CoverPresence
import ConditionalExamples

namespace GeneralizedIntervalArithmetic.CoverPresenceExamples
open ConditionalExamples

def left : Expr := .sub .x (.const (1/2))
def right : Expr := .add left left
def tree : ConditionalExpr := .iteLt .x (1/2) (.leaf left) (.leaf right)
def L : LinearInterval := inputX.sub (.exact ⟨1/2,1/2⟩)
def ranges : FiniteLinearCover := [L,L.add L]
noncomputable def curve := thresholdValue (1/2) (fun t => t-1/2) (fun t => (t-1/2)+(t-1/2))

theorem evaluates : evalConditionalCover inputX inputY tree = some ranges := by
  have hc : decideLinearLt inputX (1/2) = .unknown := by decide +kernel
  simp only [tree,evalConditionalCover,evalGuarded]
  rw [hc]
  rfl

theorem continuous_value_certificate :
    ContinuousOn curve (Set.Icc (0:ℝ) 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, ConditionalValue t 0 tree (curve t) := by
  apply conditional_threshold_certificate (1/2) (by norm_num)
  · intro t _
    exact Value.x
  · exact (continuous_id.sub continuous_const).continuousOn
  · exact ((continuous_id.sub continuous_const).add
      (continuous_id.sub continuous_const)).continuousOn
  · norm_num
  · intro t _ _
    apply ConditionalValue.leaf
    simpa [left] using (Value.sub (Value.x (x := t) (y := (0:ℝ))) (Value.const (1/2)))
  · intro t _
    apply ConditionalValue.leaf
    have h : Value t 0 left (t-1/2) := by
      simpa [left] using (Value.sub (Value.x (x := t) (y := (0:ℝ))) (Value.const (1/2)))
    exact Value.add h h

def ParameterValue (t z : ℝ) := t ∈ Set.Icc (0:ℝ) 1 ∧ z = t

theorem parameter_sound :
    (inputX.onDomain MultiplicationExamples.everywhere).Sound ParameterValue := by
  refine ⟨?_,fun _ _ h => ⟨h.1,trivial⟩,fun t h => ⟨t,h.1,rfl⟩⟩
  rintro t z ⟨_,hz⟩
  subst z
  change inputX.Contains t t
  simp [inputX,LinearInterval.Contains,LinearInterval.exact,QAffine.value]

def Values := ConditionalExpressionValues ParameterValue MultiplicationExamples.ZeroValue tree
def domain := MultiplicationExamples.everywhere.inter MultiplicationExamples.everywhere

theorem domain_contract : ranges.SoundOn domain Values :=
  evalConditionalCover_relational_sound parameter_sound
    MultiplicationExamples.zero_domain_sound evaluates

theorem representative_agreement {t z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hz : Values t z) : z = curve t := by
  obtain ⟨x,y,hx,hy,hv⟩ := hz
  rcases hx with ⟨_,hx⟩
  rcases hy with ⟨_,hy⟩
  subst x
  subst y
  exact conditional_value_unique hv (continuous_value_certificate.2 t ht)

theorem left_signs : ∀ I ∈ ranges, I.upper.atZero ≤ 0 := by
  intro I hi
  rcases List.mem_cons.mp hi with rfl | hi
  · decide +kernel
  · rcases List.mem_singleton.mp hi with rfl
    decide +kernel

theorem right_signs : ∀ I ∈ ranges, 0 ≤ I.lower.atOne := by
  intro I hi
  rcases List.mem_cons.mp hi with rfl | hi
  · decide +kernel
  · rcases List.mem_singleton.mp hi with rfl
    decide +kernel

theorem certified_conditional_root : ∃ t ∈ Set.Icc (0:ℝ) 1, Values t 0 := by
  exact cover_domain_presence domain_contract continuous_value_certificate.1
    (fun _ ht _ hz => representative_agreement ht hz)
    (fun _ _ => ⟨trivial,trivial⟩) left_signs right_signs

def holeDomain : DomainBounds ℝ := domain.inter
  ⟨fun t => t ≠ (1/2:ℝ),fun t => t ≠ (1/2:ℝ),fun _ h => h⟩
def HoleValues (t z : ℝ) := t ≠ (1/2:ℝ) ∧ Values t z

theorem hole_contract : ranges.SoundOn holeDomain HoleValues :=
  cover_domain_restrict domain_contract (fun t => t ≠ (1/2:ℝ))

theorem curve_zero_iff (t : ℝ) : curve t = 0 ↔ t = 1/2 := by
  unfold curve thresholdValue
  norm_num
  split <;> constructor <;> intro h <;> linarith

theorem hole_has_no_root : ¬ ∃ t ∈ Set.Icc (0:ℝ) 1, HoleValues t 0 := by
  rintro ⟨t,ht,hne,hv⟩
  have hz := representative_agreement ht hv
  exact hne ((curve_zero_iff t).mp hz.symm)

theorem hole_endpoint_values : (∃ z, HoleValues 0 z) ∧ (∃ z, HoleValues 1 z) := by
  constructor
  · apply cover_domain_definite hole_contract (by norm_num)
    change (True ∧ True) ∧ (0:ℝ) ≠ 1/2
    norm_num
  · apply cover_domain_definite hole_contract (by norm_num)
    change (True ∧ True) ∧ (1:ℝ) ≠ 1/2
    norm_num

theorem hole_not_definite_everywhere :
    ¬ ∀ t ∈ Set.Icc (0:ℝ) 1, holeDomain.definite t := by
  intro h
  exact (h (1/2) (by norm_num)).2 rfl

end GeneralizedIntervalArithmetic.CoverPresenceExamples
