import PartialImageTransfer
import AuditPolicy
namespace GeneralizedIntervalArithmetic.PartialImageTransferChecks
open PartialImageTransfer

theorem negative_gap_check : blocked? ({-1} : Finset ℚ) (fun q => 0 ≤ q) = true := by decide
theorem zero_root_rejected : blocked? ({0} : Finset ℚ) (fun q => 0 ≤ q) = false := by decide
theorem zero_reciprocal_check : blocked? ({0} : Finset ℚ) (fun q => q ≠ 0) = true := by decide
theorem nonzero_gap_rejected : blocked? ({1} : Finset ℚ) (fun q => q ≠ 0) = false := by decide
theorem mixed_gap_rejected : blocked? ({0,1} : Finset ℚ) (fun q => q ≠ 0) = false := by decide

/-- The omitted negative boundary has no root, so closing it is exact. -/
theorem root_open_boundary : RootTransfer.roots (Set.Icc (-1) 4) =
    RootTransfer.roots (Set.Ioc (-1) 4) := by
  rw [← root_image,← root_image]
  apply exact_of_finite_gaps (S := Set.Ioc (-1) 4) (T := Set.Icc (-1) 4)
    (fun _ h => ⟨h.1.le,h.2⟩)
    ({-1} : Finset ℚ) (fun q => (q : ℝ)) (fun q => 0 ≤ q)
  · intro x hx
    rcases eq_or_lt_of_le hx.1 with he | hl
    · exact Or.inr ⟨-1,by simp,by simpa using he.symm⟩
    · exact Or.inl ⟨hl,hx.2⟩
  · intro q _
    rw [root_domain]
    exact_mod_cast (Iff.rfl : 0 ≤ q ↔ 0 ≤ q)
  · exact negative_gap_check

/-- A genuine pole is an absent value, even though its hull contains zero. -/
theorem reciprocal_pole_closed : image reciprocal (Set.Icc (-1) 1) =
    image reciprocal (Set.Icc (-1) 1 \ {0}) := by
  apply exact_of_finite_gaps Set.diff_subset ({0} : Finset ℚ)
    (fun q => (q : ℝ)) (fun q => q ≠ 0)
  · intro x hx
    by_cases h : x = 0
    · exact Or.inr ⟨0,by simp,by simpa using h⟩
    · exact Or.inl ⟨hx,h⟩
  · intro q _
    rw [reciprocal_domain]
    exact_mod_cast (Iff.rfl : q ≠ 0 ↔ q ≠ 0)
  · exact zero_reciprocal_check

theorem reciprocal_missing_tip : (1 : ℝ) ∈ image reciprocal (Set.Icc 1 2) ∧
    (1 : ℝ) ∉ image reciprocal (Set.Ioc 1 2) := by
  constructor
  · exact ⟨1,by norm_num,by norm_num [reciprocal,PartialRealArithmetic.divRel]⟩
  · rintro ⟨x,hx,hn,he⟩
    have h : x = 1 := inv_injective (show x⁻¹ = (1:ℝ)⁻¹ by simpa only [one_div, inv_one] using he.symm)
    subst x
    exact (lt_irrefl _ hx.1)

theorem reciprocal_missing_interior : (1 : ℝ) ∉
    image reciprocal (Set.Icc (-2) 2 \ {1}) := by
  rintro ⟨x,hx,hn,he⟩
  have h : x = 1 := inv_injective (show x⁻¹ = (1:ℝ)⁻¹ by simpa only [one_div, inv_one] using he.symm)
  exact hx.2 h

theorem root_new_zero : (0 : ℝ) ∈ image root (Set.Icc (-1) 0) ∧
    (0 : ℝ) ∉ image root (Set.Ico (-1) 0) := by
  constructor
  · exact ⟨0,by norm_num,by norm_num [root]⟩
  · rintro ⟨x,hx,h0,_⟩
    exact (not_lt_of_ge h0 hx.2)

/-- Without injectivity, exact images need not imply exact defined-input sets. -/
theorem constant_counterexample :
    image (fun (_ z : ℝ) => z = 0) {0,1} = image (fun (_ z : ℝ) => z = 0) {0} ∧
    (1 : ℝ) ∉ ({0} : Set ℝ) ∧ Defined (fun (_ z : ℝ) => z = 0) 1 := by
  refine ⟨?_,by norm_num,⟨0,rfl⟩⟩
  ext z
  constructor
  · rintro ⟨_,_,hz⟩
    exact ⟨0,by simp,hz⟩
  · rintro ⟨x,hx,hz⟩
    exact ⟨x,by simp_all,hz⟩

theorem empty_image (R : ℝ → ℝ → Prop) : image R ∅ = ∅ := by
  ext z
  simp [image,GeneralFamilyDemotion.outputs]

theorem zero_only_empty : image reciprocal {0} = ∅ := by
  ext z
  simp [image,GeneralFamilyDemotion.outputs,reciprocal,PartialRealArithmetic.divRel]

/-- Same output image does not preserve universal definedness of input sets. -/
theorem totality_not_preserved :
    (∀ x ∈ ({1} : Set ℝ), Defined reciprocal x) ∧
    ¬ (∀ x ∈ ({0,1} : Set ℝ), Defined reciprocal x) := by
  constructor
  · intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact (reciprocal_domain 1).2 (by norm_num)
  · intro h
    exact ((reciprocal_domain 0).1 (h 0 (by simp))) rfl

#audit_namespace GeneralizedIntervalArithmetic.PartialImageTransferChecks
end GeneralizedIntervalArithmetic.PartialImageTransferChecks
