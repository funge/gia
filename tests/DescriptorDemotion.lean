import DescriptorDemotion
import AuditPolicy
namespace GeneralizedIntervalArithmetic.DescriptorDemotionChecks
open DescriptorDemotion DomainConstraints

theorem singleton_hull : NumberPromotion.hull ({1/2}:Set ℝ) = Set.Icc 0 1 := by
  rw [NumberPromotion.finite_formula (Set.singleton_nonempty _) bddBelow_singleton bddAbove_singleton]
  ext x
  norm_num [ExtendedImageHull.interval]
  norm_cast
  simp

/-- Exact true classification may weaken to mixed; zero is admitted by the
converted descriptor but does not replace the original nonzero witness. -/
theorem nonzero_weakens :
    (domain (fun _ : Unit => ({1/2}:Set ℝ)) (fun x => x≠0)).definite () ∧
    ¬ (domain (fun _ : Unit => NumberPromotion.hull ({1/2}:Set ℝ)) (fun x => x≠0)).definite () ∧
    (domain (fun _ : Unit => NumberPromotion.hull ({1/2}:Set ℝ)) (fun x => x≠0)).possible () := by
  rw [definite_iff,definite_iff,possible_iff,singleton_hull]
  refine ⟨⟨⟨1/2,by simp⟩,by norm_num⟩, ?_, ⟨1,by norm_num,by norm_num⟩⟩
  rintro ⟨_,h⟩
  exact h 0 (by norm_num) rfl

theorem unbounded_mixed :
    ¬ (domain (fun _ : Unit => NumberPromotion.hull Set.univ) (fun x => x≠0)).definite () ∧
    (domain (fun _ : Unit => NumberPromotion.hull Set.univ) (fun x => x≠0)).possible () := by
  constructor
  · intro h
    exact ((definite_iff _ _ ()).mp h).2 0 (NumberPromotion.sound _ (Set.mem_univ _)) rfl
  · exact (possible_iff _ _ ()).mpr ⟨1,NumberPromotion.sound _ (Set.mem_univ _),by norm_num⟩

theorem empty_stays_empty :
    ¬ (domain (fun _ : Unit => NumberPromotion.hull ∅) (fun _ => True)).possible () ∧
    ¬ (domain (fun _ : Unit => NumberPromotion.hull ∅) (fun _ => True)).definite () := by
  simp [possible_iff,definite_iff,NumberPromotion.empty]

/-- Actual external-domain holes survive the conversion and guard. -/
theorem external_hole_preserved (x : ℝ) :
    ((exactDomain (fun _ : Unit => False)).inter
      (domain (fun _ => NumberPromotion.hull Set.univ) (fun x => x≠0))).Compatible ()
      (False ∧ x≠0) := by
  apply guarded_integer_compatible
  · exact ⟨id,id⟩
  · exact fun h => h.elim

theorem retained_nonzero_witness :
    (domain (fun _ : Unit => NumberPromotion.hull ({1/2}:Set ℝ)) (fun x => x≠0)).Compatible ()
      ((1/2:ℝ)≠0) :=
  witness_compatible _ _ () _ (NumberPromotion.sound _ (by simp))

theorem retained_lambda_control :
    (domain (fun _ : Unit => ({.undefined, .finite 0} : Set ExceptionalComparisons.Value))
      (fun v => v ≠ .undefined)).Compatible () False := by
  simpa [ExceptionalComparisons.bound] using retained_tag_domain
    (fun _ : Unit => ({.undefined, .finite 0} : Set ExceptionalComparisons.Value))
    () .undefined (by simp)

theorem infinite_tag_is_not_lambda :
    (∃ b, ExceptionalComparisons.bound .posInf = some b) ∧
    ¬ (∃ b, ExceptionalComparisons.bound .undefined = some b) := by
  simp [ExceptionalComparisons.bound]

end GeneralizedIntervalArithmetic.DescriptorDemotionChecks
#audit_namespace GeneralizedIntervalArithmetic.DescriptorDemotionChecks
