import RootTransfer
import AuditPolicy
namespace GeneralizedIntervalArithmetic.RootTransferChecks
open RootTransfer
local notation "Tag" => ExceptionalComparisons.Value

def negative : Set ℝ := Set.Ioo (-1) 0

theorem negative_hull : ExtendedImageHull.hull negative = Set.Icc (-1) 0 := by
  rw [ExtendedImageHull.finite_agreement (S:=negative)
    (by exact ⟨-1/2,by norm_num [negative]⟩)
    ⟨-1,fun _ h => h.1.le⟩ ⟨0,fun _ h => h.2.le⟩]
  simp [ExactImageHull.hull,negative,csInf_Ioo (by norm_num : (-1:ℝ)<0),
    csSup_Ioo (by norm_num : (-1:ℝ)<0)]

theorem negative_roots : roots negative = ∅ := by
  ext z
  rw [root_iff]
  simp only [negative,Set.mem_Ioo,Set.mem_empty_iff_false,iff_false,not_and]
  intro _ hz
  nlinarith [sq_nonneg z]

theorem introduced_zero : (0:ℝ) ∈ roots (ExtendedImageHull.hull negative) := by
  rw [root_iff,negative_hull]; norm_num

theorem no_unconditional_commutation : roots (ExtendedImageHull.hull negative) ≠
    ExtendedImageHull.hull (roots negative) := by
  rw [negative_roots,ExtendedImageHull.empty_hull]
  intro h
  have hi := introduced_zero
  rw [h] at hi
  exact hi

/-- Even without a domain change, hull conversion can fill an output hole. -/
theorem hole_added : (1:ℝ) ∈ roots (ExtendedImageHull.hull {(0:ℝ),4}) ∧
    (1:ℝ) ∉ roots {(0:ℝ),4} := by
  constructor
  · rw [root_iff]
    refine ⟨by norm_num,?_⟩
    have hl := (ExtendedImageHull.sound {(0:ℝ),4} (show (0:ℝ) ∈ {(0:ℝ),4} by simp)).1
    have hu := (ExtendedImageHull.sound {(0:ℝ),4} (show (4:ℝ) ∈ {(0:ℝ),4} by simp)).2
    exact ⟨hl.trans (by norm_num), (EReal.coe_le_coe_iff.mpr (by norm_num : (1:ℝ)^2≤4)).trans hu⟩
  · rw [root_iff]; norm_num

theorem closed_range : roots (Set.Icc (-1:ℝ) 4) = Set.Icc 0 2 := by
  ext z
  rw [root_iff]
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨h0,_,hu⟩; exact ⟨h0,by nlinarith⟩
  · rintro ⟨h0,hu⟩; exact ⟨h0,by nlinarith [sq_nonneg z],by nlinarith⟩

theorem closed_exact : roots (ExtendedImageHull.hull (Set.Icc (-1:ℝ) 4)) = Set.Icc 0 2 := by
  have h := interval_exact ((-1:ℝ):EReal) ((4:ℝ):EReal)
  simp only [ExtendedImageHull.interval,EReal.coe_le_coe_iff] at h
  exact h.trans closed_range

theorem unbounded_range : roots Set.univ = Set.Ici (0:ℝ) := by
  ext z; rw [root_iff]; simp

theorem empty_roots : roots ∅ = ∅ := by ext z; rw [root_iff]; simp

def negativeTags : Set Tag := ExceptionalComparisons.Value.finite '' negative

theorem finite_part : TaggedConversion.finitePart negativeTags = negative := by
  ext x; simp [TaggedConversion.finitePart,negativeTags]

theorem zero_observation_new :
    some (.finite 0) ∈ observations (TaggedConversion.lift ExtendedImageHull.hull negativeTags) ∧
    some (.finite 0) ∉ observations negativeTags := by
  rw [finite_graph,TaggedConversion.finitePart_lift,finite_part,finite_graph,finite_part,negative_roots]
  exact ⟨introduced_zero,by simp⟩

theorem lambda_preserved : some .undefined ∈ observations negativeTags ∧
    some .undefined ∈ observations (TaggedConversion.lift ExtendedImageHull.hull negativeTags) := by
  have h : some .undefined ∈ observations negativeTags := by
    rw [lambda_graph,finite_part]
    exact ⟨-1/2,by norm_num [negative],by norm_num⟩
  exact ⟨h,(statuses_exact negativeTags).1.mpr h⟩

theorem exceptional_inputs_missing :
    none ∈ observations ({.posInf,.negInf,.undefined} : Set Tag) := by
  rw [missing_graph]; simp

theorem no_infinite_root : some .posInf ∉ observations ({.posInf} : Set Tag) :=
  (no_infinite_results _).2

end GeneralizedIntervalArithmetic.RootTransferChecks
#audit_namespace GeneralizedIntervalArithmetic.RootTransferChecks
