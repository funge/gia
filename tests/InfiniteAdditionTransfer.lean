import InfiniteAdditionTransfer
import AuditPolicy
namespace GeneralizedIntervalArithmetic.InfiniteAdditionTransferChecks
open ExceptionalComparisons InfiniteAdditionTransfer
local notation "Tag" => ExceptionalComparisons.Value

theorem empty : observations ∅ = ∅ := by simp [observations]

theorem singleton_finite (x : ℝ) : observations {ExceptionalComparisons.Value.finite x} = {some ExceptionalComparisons.Value.posInf} := by
  simp [observations,addObservation]

theorem singleton_infinite : observations {ExceptionalComparisons.Value.posInf} = {some ExceptionalComparisons.Value.posInf} := by
  simp [observations,addObservation]

theorem singleton_lambda : observations {ExceptionalComparisons.Value.undefined} = {none} := by
  simp [observations,addObservation]

theorem no_lambda_result : some ExceptionalComparisons.Value.undefined ∉ observations {ExceptionalComparisons.Value.undefined} := by
  rw [singleton_lambda]; simp

theorem mixed : observations {ExceptionalComparisons.Value.finite 3,ExceptionalComparisons.Value.negInf} = {some ExceptionalComparisons.Value.posInf,none} := by
  rw [observations,Set.image_insert_eq,Set.image_singleton]
  rfl

def allFinite : Set Tag := Set.range ExceptionalComparisons.Value.finite

theorem unbounded_observations : observations allFinite = {some ExceptionalComparisons.Value.posInf} := by
  ext r
  rw [graph]
  have hf : (TaggedConversion.finitePart allFinite).Nonempty := ⟨0,0,rfl⟩
  simp only [hf,true_or,and_true]
  simp [allFinite]

theorem unbounded_no_literal_tag : ExceptionalComparisons.Value.posInf ∉ allFinite ∧ ExceptionalComparisons.Value.negInf ∉ allFinite ∧
    ExceptionalComparisons.Value.undefined ∉ allFinite := by simp [allFinite]

theorem hull_does_not_insert_infinity : ExceptionalComparisons.Value.posInf ∉ TaggedConversion.lift ExtendedImageHull.hull allFinite := by
  change ExceptionalComparisons.Value.posInf ∉ allFinite
  exact unbounded_no_literal_tag.1

/-- Empty-preservation is essential to conversion: a converter that invents a
finite witness changes the observation set. -/
theorem invented_value : some ExceptionalComparisons.Value.posInf ∈ observations
    (TaggedConversion.lift (fun _ => Set.univ) ∅) := by
  rw [graph]
  exact Or.inl ⟨rfl,Or.inl ⟨0,Set.mem_univ _⟩⟩

theorem invention_not_exact : observations (TaggedConversion.lift (fun _ => Set.univ) ∅) ≠
    observations ∅ := by
  intro h
  have hi := invented_value
  rw [h,empty] at hi
  exact hi

/-- Missing coverage is preserved along with the successful result. -/
theorem mixed_transfer : observations (TaggedConversion.lift ExtendedImageHull.hull
    {ExceptionalComparisons.Value.finite 3,ExceptionalComparisons.Value.negInf}) = {some ExceptionalComparisons.Value.posInf,none} := by
  rw [hull_observations,mixed]

/-- Do not infer commutativity to fill unmodeled rows. -/
theorem reverse_unmodeled : addObservation ExceptionalComparisons.Value.posInf (ExceptionalComparisons.Value.finite 3) = none := rfl

theorem no_finite_output : TaggedConversion.finitePart (results allFinite) = ∅ :=
  finite_results_empty _

end GeneralizedIntervalArithmetic.InfiniteAdditionTransferChecks
#audit_namespace GeneralizedIntervalArithmetic.InfiniteAdditionTransferChecks
