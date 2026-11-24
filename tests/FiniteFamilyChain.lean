import FiniteFamilyChain
import ExceptionalComparisons
import AuditPolicy
namespace GeneralizedIntervalArithmetic.FiniteFamilyChainChecks
open FiniteFamilyChain QuadraticFamilies

noncomputable def exactForm (a : Form 1) : Bounds 1 := ⟨a,a,fun _ _=>le_rfl⟩
noncomputable def bubble : Bounds 1 := exactForm (ofCoefficients 0 1 (-1))
noncomputable def square : Bounds 1 := exactForm (ofCoefficients 0 0 1)

theorem bubble_hull : (demote bubble).hull.lo=0 ∧ (demote bubble).hull.hi=1/4 := by
  norm_num [demote,bubble,exactForm,formBounds,ofCoefficients,LinearInterval.hull,
    LinearInterval.add,LinearInterval.exact,QAffine.add,QAffine.productBounds,QAffine.curvature]

theorem strict_exclusion : ¬ (demote bubble).hull.Contains (1/2) ∧
    bubble.constantHull.Contains (1/2) := by
  constructor
  · simp only [QInterval.Contains,bubble_hull.1,bubble_hull.2]; norm_num
  · norm_num [Bounds.constantHull,bubble,exactForm,ofCoefficients,Form.lo,Form.hi,
      MultiAffineFamilies.Form.lo,MultiAffineFamilies.Form.hi,QInterval.Contains]

/-- The quadratic interior maximum is enclosed through the actual converter. -/
theorem bubble_midpoint : (demote bubble).Contains (1/2) (1/4:ℝ) := by
  apply demote_encloses (t:=fun _=>1/2) _ (fun _=>by norm_num)
  norm_num [bubble,exactForm,Bounds.Contains,coefficients_value]

theorem demotion_is_not_exact : (demote square).Contains 0 (-1/4:ℝ) ∧
    ¬ square.Contains (fun _=>0) (-1/4:ℝ) := by
  norm_num [demote,square,exactForm,formBounds,ofCoefficients,LinearInterval.Contains,
    LinearInterval.add,LinearInterval.exact,QAffine.add,QAffine.productBounds,QAffine.curvature,
    QAffine.value,Bounds.Contains,Form.value,MultiAffineFamilies.Form.value]

/-- Two valid demotions need not be ordered by their constant hulls. -/
theorem affine_hull_not_always_better :
    (demote square).hull.Contains (-1/4:ℝ) ∧ ¬ square.constantHull.Contains (-1/4:ℝ) := by
  norm_num [demote,square,exactForm,formBounds,ofCoefficients,LinearInterval.hull,
    LinearInterval.add,LinearInterval.exact,QAffine.add,QAffine.productBounds,QAffine.curvature,
    QInterval.Contains,Bounds.constantHull,Form.lo,Form.hi,
    MultiAffineFamilies.Form.lo,MultiAffineFamilies.Form.hi]

theorem square_not_exact_affine : ¬ ∃ a:QAffine, ∀t∈Set.Icc (0:ℝ) 1,
    a.value t = (ofCoefficients 0 0 1).value (fun _=>t) := by
  rintro ⟨a,h⟩
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have hh := h (1/2) (by norm_num)
  norm_num [QAffine.value,coefficients_value] at h0 h1 hh
  rw [h0] at hh
  norm_num at hh
  linarith

theorem shared_parameter_preserved :
    (product (MultiAffineFamilies.fromQAffine ⟨0,1⟩)
      (MultiAffineFamilies.fromQAffine ⟨1,0⟩)).value (fun _=>1) = 0 ∧
    (QAffine.value ⟨0,1⟩ 1)*(QAffine.value ⟨1,0⟩ 0)=1 := by
  norm_num [product_value,MultiAffineFamilies.fromQAffine_value,QAffine.value]

noncomputable def hole (t : Fin 1 → ℝ) (_ : Unit) : Prop := t 0 ≠ 1/2

theorem hole_not_filled : (demote square).Contains (1/2) (1/4:ℝ) ∧
    ¬ ∃z, relation square hole (fun _=>1/2) () z := by
  constructor
  · apply demote_encloses (t:=fun _=>1/2) _ (fun _=>by norm_num)
    norm_num [square,exactForm,Bounds.Contains,coefficients_value]
  · simp [relation,hole]

theorem restricted_chain :
    GeneralFamilyDemotion.Sound (fun _=>{z|(demote square).hull.Contains z})
      (exactInputDomain (fun _ (_:Unit)=>True) (relation square hole))
      (fun _ (_:Unit)=>True) (relation square hole) :=
  (partial_chain square (fun _ (_:Unit)=>True) hole).2

noncomputable def uncertainSquare : Bounds 1 :=
  ⟨ofCoefficients 0 0 1,ofCoefficients (1/2) 0 1,by
    intro t ht; simp [coefficients_value]⟩

theorem interval_values_retained {t δ : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hδ : δ∈Set.Icc (0:ℝ) (1/2)) :
    (demote uncertainSquare).Contains t (t^2+δ) := by
  apply demote_encloses (t:=fun _=>t) _ (fun _=>ht)
  change _ ≤ _ ∧ _ ≤ _
  simp only [uncertainSquare,coefficients_value]
  constructor <;> norm_num <;> linarith [hδ.1,hδ.2]

/-- Concrete exceptional boundary: no finite rational coefficient is +∞. -/
theorem no_finite_infinity (q : ℚ) : ((q:ℝ):EReal) ≠ ⊤ := by simp

theorem no_finite_unbounded_constant (I : QInterval) : ¬ ∀x:ℝ,I.Contains x := by
  intro h
  have hh := (h ((I.hi:ℝ)+1)).2
  linarith

/-- Existing source semantics shows why finite membership guards cannot simply
be reused for λ; no exceptional arithmetic row is invented here. -/
theorem lambda_is_not_a_finite_member (l u : ℝ) :
    ExceptionalComparisons.observe .lt .undefined (.finite l) = some false ∧
    ExceptionalComparisons.observe .lt (.finite u) .undefined = some false ∧
    ExceptionalComparisons.bound .undefined = none :=
  ExceptionalComparisons.undefined_passes_negated_tests l u

end GeneralizedIntervalArithmetic.FiniteFamilyChainChecks
#audit_namespace GeneralizedIntervalArithmetic.FiniteFamilyChainChecks
