import TaggedConversion
import AuditPolicy
namespace GeneralizedIntervalArithmetic.TaggedConversionChecks
open TaggedConversion
local notation "Tag" => ExceptionalComparisons.Value

/-- Kernel decision checks the actual tag-erasing functions, not a quotient bit. -/
theorem erased_signed_infinities :
    kind (restoreFinite (finiteOnly .negInf)) = .undefined ∧
    kind (restoreFinite (finiteOnly .posInf)) = .undefined ∧
    kind (restoreFinite (finiteOnly .undefined)) = .undefined ∧
    kind (restoreFinite (finiteOnly (.finite 0))) = .finite := by decide

theorem all_categories_retained (x : ℝ) :
    let S : Set Tag := {.finite x,.negInf,.posInf,.undefined}
    ∀ v ∈ S, v ∈ lift NumberPromotion.hull (lift ExtendedImageHull.hull S) := by
  intro S v hv
  exact lift_sound _ NumberPromotion.sound _ (lift_sound _ ExtendedImageHull.sound _ hv)

theorem chain_exact (S : Set Tag) :
    lift NumberPromotion.hull (lift ExtendedImageHull.hull S) =
      lift (NumberPromotion.hull ∘ ExtendedImageHull.hull) S := lift_comp _ _ _

theorem real_unbounded_not_infinity :
    .posInf ∉ lift NumberPromotion.hull {v : Tag | ∃ x, v = .finite x} ∧
    .negInf ∉ lift NumberPromotion.hull {v : Tag | ∃ x, v = .finite x} ∧
    .undefined ∉ lift NumberPromotion.hull {v : Tag | ∃ x, v = .finite x} := by
  change (¬ ∃ x : ℝ, ExceptionalComparisons.Value.posInf = ExceptionalComparisons.Value.finite x) ∧
    (¬ ∃ x : ℝ, ExceptionalComparisons.Value.negInf = ExceptionalComparisons.Value.finite x) ∧
    (¬ ∃ x : ℝ, ExceptionalComparisons.Value.undefined = ExceptionalComparisons.Value.finite x)
  simp

theorem empty_retained : lift NumberPromotion.hull ∅ = ∅ :=
  lift_empty _ NumberPromotion.empty

theorem defined_bits_exact (S : Unit → Set Tag) :
    ((DescriptorDemotion.domain (fun p => lift NumberPromotion.hull (S p))
      (fun v => v ≠ .undefined)).definite () ↔
      (DescriptorDemotion.domain S (fun v => v ≠ .undefined)).definite ()) ∧
    ((DescriptorDemotion.domain (fun p => lift NumberPromotion.hull (S p))
      (fun v => v ≠ .undefined)).possible () ↔
      (DescriptorDemotion.domain S (fun v => v ≠ .undefined)).possible ()) :=
  definedness_exact _ NumberPromotion.sound NumberPromotion.empty S ()

theorem chain_defined_bits (S : Unit → Set Tag) :
    ((DescriptorDemotion.domain
      (fun p => lift NumberPromotion.hull (lift ExtendedImageHull.hull (S p)))
      (fun v => v ≠ .undefined)).definite () ↔
      (DescriptorDemotion.domain S (fun v => v ≠ .undefined)).definite ()) ∧
    ((DescriptorDemotion.domain
      (fun p => lift NumberPromotion.hull (lift ExtendedImageHull.hull (S p)))
      (fun v => v ≠ .undefined)).possible () ↔
      (DescriptorDemotion.domain S (fun v => v ≠ .undefined)).possible ()) := by
  have hc := definedness_exact _ ExtendedImageHull.sound ExtendedImageHull.empty_hull S ()
  have hd := definedness_exact _ NumberPromotion.sound NumberPromotion.empty
    (fun p => lift ExtendedImageHull.hull (S p)) ()
  exact ⟨hd.1.trans hc.1,hd.2.trans hc.2⟩

/-- Dropping the empty-preservation premise really invents a defined alternative. -/
theorem empty_preservation_needed :
    (∃ v ∈ lift (fun _ => Set.univ) ({.undefined} : Set Tag), v ≠ .undefined) ∧
    ¬ (∃ v ∈ ({.undefined} : Set Tag), v ≠ .undefined) := by
  constructor
  · exact ⟨.finite 0,(show (0:ℝ) ∈ Set.univ from Set.mem_univ _),by intro h; cases h⟩
  · simp

theorem external_hole (S : Unit → Set Tag) (v : Tag) :
    ((DomainConstraints.exactDomain (fun _ : Unit => False)).inter
      (DescriptorDemotion.domain
        (fun p => lift NumberPromotion.hull (lift ExtendedImageHull.hull (S p)))
        (fun v => v ≠ .undefined))).Compatible () (False ∧ v ≠ .undefined) := by
  apply guarded_witness _ _ ExtendedImageHull.sound NumberPromotion.sound
  · exact ⟨id,id⟩
  · exact fun h => h.elim

end GeneralizedIntervalArithmetic.TaggedConversionChecks
#audit_namespace GeneralizedIntervalArithmetic.TaggedConversionChecks
