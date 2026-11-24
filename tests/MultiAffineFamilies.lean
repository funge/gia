import MultiAffineFamilies
import AuditPolicy
namespace GeneralizedIntervalArithmetic.MultiAffineFamiliesChecks
open MultiAffineFamilies

noncomputable def mixed : Form 2 := ⟨2,![3,-5]⟩
theorem mixed_extrema : mixed.lo = -3 ∧ mixed.hi = 5 := by
  norm_num [mixed,Form.lo,Form.hi,Fin.sum_univ_two]

theorem actual_corners :
    mixed.value ![0,1] = -3 ∧ mixed.value ![1,0] = 5 := by
  norm_num [mixed,Form.value,Fin.sum_univ_two]

noncomputable def diagonal : Form 2 := ⟨0,![1,-1]⟩
noncomputable def zero : Form 2 := ⟨0,fun _=>0⟩

/-- The cube's two diagonal vertices do not certify order on all its vertices. -/
theorem diagonal_checks_fail :
    diagonal.value ![0,0] = 0 ∧ diagonal.value ![1,1] = 0 ∧
    Cube ![0,1] ∧ diagonal.value ![0,1] < 0 ∧
    ¬ (zero.sub diagonal).hi ≤ 0 := by
  norm_num [diagonal,zero,Form.value,Form.sub,Form.hi,Fin.sum_univ_two,Cube,Fin.forall_fin_two]

theorem same_vector_cancellation (t : Fin 2 → ℝ) :
    (diagonal.sub diagonal).value t = 0 := by rw [sub_value]; ring

/-- Forgetting the joint vector allows a spurious nonzero difference. -/
theorem independent_vectors_lose_cancellation :
    Cube ![1,0] ∧ Cube ![0,1] ∧
    diagonal.value ![1,0] - diagonal.value ![0,1] = 2 := by
  norm_num [Cube,Fin.forall_fin_two,diagonal,Form.value,Fin.sum_univ_two]

noncomputable def exactMixed : Bounds 2 := ⟨mixed,mixed,by
  apply (order_iff _ _).mp; intro t ht; exact le_rfl⟩

theorem least_projected_hull :
    exactMixed.hull.lo = -3 ∧ exactMixed.hull.hi = 5 := mixed_extrema

theorem constant_demotion_loses_fiber :
    exactMixed.hull.Contains (-3) ∧ ¬ exactMixed.Contains ![0,0] (-3) := by
  norm_num [QInterval.Contains,Bounds.hull,Bounds.Contains,exactMixed,mixed,
    Form.lo,Form.hi,Form.value,Fin.sum_univ_two]

/-- Zero parameters is the constant family, with no hidden nonempty-index premise. -/
theorem no_parameters (q : ℚ) (t : Fin 0 → ℝ) :
    (Form.mk q (fun i=>Fin.elim0 i)).value t = (q:ℝ) ∧
    (Form.mk q (fun i=>Fin.elim0 i)).lo = q ∧
    (Form.mk q (fun i=>Fin.elim0 i)).hi = q := by
  simp [Form.value,Form.lo,Form.hi]

theorem embedded_shrinking (t : Fin 1 → ℝ) (z : ℝ) :
    (fromLinear LinearFamilyEquality.shrinking).Contains t z ↔
      LinearFamilyEquality.shrinking.Contains (t 0) z := fromLinear_contains _ _ _

theorem restricted_domain_is_smaller (t : Fin 2 → ℝ) (h : t 0 = t 1) :
    diagonal.value t = 0 := by
  simp [diagonal,Form.value,Fin.sum_univ_two,h]

theorem negative_scaling :
    (Form.scale (-2) mixed).lo = -10 ∧ (Form.scale (-2) mixed).hi = 6 := by
  norm_num [Form.scale,mixed,Form.lo,Form.hi,Fin.sum_univ_two]

/-- The existing same-witness demotion theorem is directly applicable. -/
theorem sound_projection {W : Type*} (A : (Fin 2 → ℝ) → W → Prop)
    (R : (Fin 2 → ℝ) → W → ℝ → Prop)
    (h : GeneralFamilyDemotion.Sound (fun t=>{z|exactMixed.Contains t z})
      (DomainConstraints.exactDomain Cube) A R) :
    GeneralFamilyDemotion.Sound (fun _=>{z|exactMixed.hull.Contains z})
      (DomainConstraints.exactDomain Cube) A R :=
  GeneralFamilyDemotion.sound_demote h (constant_demotion _)

end GeneralizedIntervalArithmetic.MultiAffineFamiliesChecks
#audit_namespace GeneralizedIntervalArithmetic.MultiAffineFamiliesChecks
