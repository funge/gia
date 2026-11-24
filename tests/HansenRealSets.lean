import HansenRealSets
import AuditPolicy
namespace GeneralizedIntervalArithmetic.HansenRealSetsChecks
open HansenRealSets

def free : Fin 1 → Set ℝ := fun _ => Set.univ

theorem open_image : values (Set.Ioo (0:ℝ) 1) free (fun _=>0) = Set.Ioo 0 1 :=
  zero_weights _ _ (fun _ => Set.univ_nonempty)

theorem open_interior : (1/2:ℝ) ∈ values (Set.Ioo (0:ℝ) 1) free (fun _=>0) := by
  rw [open_image]; norm_num

theorem boundary_absent : (0:ℝ) ∉ values (Set.Ioo (0:ℝ) 1) free (fun _=>0) := by
  rw [open_image]; simp

theorem open_bounds : ExtendedImageHull.lower (values (Set.Ioo (0:ℝ) 1) free (fun _=>0)) = (0:ℝ) ∧
    ExtendedImageHull.upper (values (Set.Ioo (0:ℝ) 1) free (fun _=>0)) = (1:ℝ) := by
  rw [open_image]
  constructor
  · rw [ExtendedImageHull.lower_finite (Set.nonempty_Ioo.mpr (by norm_num))
      (show BddBelow (Set.Ioo (0:ℝ) 1) from ⟨0,fun _ hx=>hx.1.le⟩)]
    simp
  · rw [ExtendedImageHull.upper_finite (Set.nonempty_Ioo.mpr (by norm_num))
      (show BddAbove (Set.Ioo (0:ℝ) 1) from ⟨1,fun _ hx=>hx.2.le⟩)]
    simp

theorem open_not_hull : ExtendedImageHull.hull (values (Set.Ioo (0:ℝ) 1) free (fun _=>0)) ≠
    values (Set.Ioo (0:ℝ) 1) free (fun _=>0) := by
  intro h
  apply boundary_absent
  rw [← h]
  change ExtendedImageHull.lower _ ≤ (0:ℝ) ∧ (0:ℝ) ≤ ExtendedImageHull.upper _
  rw [open_bounds.1,open_bounds.2]
  norm_num

theorem whole_image : values Set.univ free (fun _=>0) = Set.univ :=
  zero_weights _ _ (fun _ => Set.univ_nonempty)

theorem whole_bounds : ExtendedImageHull.lower (values Set.univ free (fun _=>0)) = ⊥ ∧
    ExtendedImageHull.upper (values Set.univ free (fun _=>0)) = ⊤ := by
  rw [whole_image]
  exact ⟨ExtendedImageHull.lower_unbounded not_bddBelow_univ,
    ExtendedImageHull.upper_unbounded not_bddAbove_univ⟩

/-- An absent coefficient cannot be erased just because its weight is zero. -/
theorem empty_zero : values {0} (fun _ : Fin 1 => ∅) (fun _=>0) = ∅ :=
  empty_coefficient _ _ _ 0 rfl

theorem empty_bounds : ExtendedImageHull.lower (values {0} (fun _ : Fin 1 => ∅) (fun _=>0)) = ⊤ ∧
    ExtendedImageHull.upper (values {0} (fun _ : Fin 1 => ∅) (fun _=>0)) = ⊥ := by
  rw [empty_zero]; exact ExtendedImageHull.empty_bounds

/-- A genuine unbounded slope coefficient, not just an unbounded offset. -/
theorem free_slope : values {0} free (fun _=>1) = Set.univ := by
  ext z; simp only [Set.mem_univ,iff_true]
  exact ⟨(0,fun _=>z),⟨rfl,fun _=>Set.mem_univ _⟩,by simp [HansenCoefficients.value]⟩

theorem positive_image : values (Set.Ioi (0:ℝ)) free (fun _=>0) = Set.Ioi 0 :=
  zero_weights _ _ (fun _ => Set.univ_nonempty)

theorem positive_bounds : ExtendedImageHull.lower (values (Set.Ioi (0:ℝ)) free (fun _=>0)) = (0:ℝ) ∧
    ExtendedImageHull.upper (values (Set.Ioi (0:ℝ)) free (fun _=>0)) = ⊤ := by
  rw [positive_image]
  constructor
  · rw [ExtendedImageHull.lower_finite (Set.nonempty_Ioi) bddBelow_Ioi]
    simp
  · apply ExtendedImageHull.upper_unbounded
    intro h
    obtain ⟨b,hb⟩ := h
    have hh := hb (show max b 0 + 1 ∈ Set.Ioi (0:ℝ) by simp only [Set.mem_Ioi]; linarith [le_max_right b 0])
    linarith [le_max_left b 0]

/-- Without convex coefficients, even a strict interior point can be absent. -/
theorem disconnected : values {(-1:ℝ),1} free (fun _=>0) = {(-1:ℝ),1} :=
  zero_weights _ _ (fun _ => Set.univ_nonempty)

theorem gap : (0:ℝ) ∉ values {(-1:ℝ),1} free (fun _=>0) := by rw [disconnected]; norm_num

theorem free_negative_slope : values {0} free (fun _=>-2) = Set.univ := by
  ext z; simp only [Set.mem_univ,iff_true]
  refine ⟨(0,fun _=>-z/2),⟨rfl,fun _=>Set.mem_univ _⟩,?_⟩
  simp [HansenCoefficients.value]

theorem free_zero_slope : values {(3:ℝ)} free (fun _=>0) = {3} :=
  zero_weights _ _ (fun _ => Set.univ_nonempty)

def finiteTags : Set ExceptionalComparisons.Value :=
  ExceptionalComparisons.Value.finite '' values Set.univ free (fun _=>0)

theorem unbounded_not_infinite :
    .posInf ∉ TaggedConversion.lift ExtendedImageHull.hull finiteTags ∧
    .negInf ∉ TaggedConversion.lift ExtendedImageHull.hull finiteTags ∧
    .undefined ∉ TaggedConversion.lift ExtendedImageHull.hull finiteTags := by
  change .posInf ∉ finiteTags ∧ .negInf ∉ finiteTags ∧ .undefined ∉ finiteTags
  simp [finiteTags]

theorem preserve_explicit_lambda : .undefined ∈ TaggedConversion.lift ExtendedImageHull.hull
    (insert .undefined finiteTags) := by
  change .undefined ∈ insert .undefined finiteTags
  exact Set.mem_insert _ _

end GeneralizedIntervalArithmetic.HansenRealSetsChecks
#audit_namespace GeneralizedIntervalArithmetic.HansenRealSetsChecks
