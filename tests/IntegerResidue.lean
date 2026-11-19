import IntegerResidue
import AuditPolicy

namespace GeneralizedIntervalArithmetic.IntegerResidueChecks
open IntegerResidue

theorem parity (x : ℝ) : HasResidue 2 0 (2*(⌊x⌋ : ℤ)) := by
  exact ⟨⌊x⌋, by push_cast; ring⟩

theorem hull (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    0 ≤ (2 : ℝ)*(⌊x⌋ : ℤ) ∧ 2*(⌊x⌋ : ℤ) ≤ (2 : ℝ) := by
  have hn : (0 : ℤ) ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx.1
  have hl : (0 : ℝ) ≤ (⌊x⌋ : ℤ) := by exact_mod_cast hn
  constructor
  · positivity
  · nlinarith [Int.floor_le x]

theorem hull_least (L U : ℝ)
    (h : ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 → L ≤ 2*(⌊x⌋ : ℤ) ∧ 2*(⌊x⌋ : ℤ) ≤ U) :
    L ≤ 0 ∧ 2 ≤ U := by
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  norm_num at h0 h1
  exact ⟨h0.1,h1.2⟩

theorem parity_window (x : ℝ) : ¬ ((1/2 : ℝ) ≤ 2*(⌊x⌋ : ℤ) ∧
    2*(⌊x⌋ : ℤ) ≤ (3/2 : ℝ)) := by
  apply window_exclusion (d := 2) (r := 0) (by norm_num) (parity x)
  norm_num

theorem hull_overlaps : ∃ z : ℝ, (0 ≤ z ∧ z ≤ 2) ∧ 1/2 ≤ z ∧ z ≤ 3/2 := by
  exact ⟨1, by norm_num⟩

theorem real_term_falsifier : ∃ x y : ℝ,
    (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1) ∧ 2*(⌊x⌋ : ℤ)+2*y = 1 := by
  exact ⟨0,1/2,by norm_num⟩

theorem half_not_integer : ¬ IntegerValue (1/2) := by
  rintro ⟨n,hn⟩
  have hp : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hq : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  omega

theorem closed_boundary_not_excluded : HasResidue 2 0 (2 : ℝ) ∧ (1/2 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 2 := by
  exact ⟨⟨1,by norm_num⟩,by norm_num,le_rfl⟩

theorem negative_window (x : ℝ) : ¬ ((-3/2 : ℝ) ≤ 2*(⌊x⌋ : ℤ) ∧
    2*(⌊x⌋ : ℤ) ≤ (-1/2 : ℝ)) := by
  apply window_exclusion (d := 2) (r := 0) (by norm_num) (parity x)
  norm_num

theorem checked_affine (x : ℝ) : HasResidue 4 1 (8*(⌈x⌉ : ℤ)+9) := by
  exact affine_residue (ceil_integer x) 8 9 4 1 (by norm_num) (by norm_num)

def partialParity (D : ℝ → Prop) (x z : ℝ) : Prop :=
  D x ∧ 0 ≤ x ∧ x ≤ 1 ∧ z = 2*(⌊x⌋ : ℤ)

def parityEnclosure (D : ℝ → Prop) : PartialEnclosure ℝ :=
  ⟨⟨fun _ => 0, fun _ => 2⟩,
   ⟨fun x => D x ∧ 0 ≤ x ∧ x ≤ 1, fun x => D x ∧ 0 ≤ x ∧ x ≤ 1, fun _ h => h⟩⟩

theorem partial_sound (D : ℝ → Prop) : (parityEnclosure D).Sound (partialParity D) := by
  refine ⟨?_,?_,?_⟩
  · rintro x z ⟨_,hx,hy,rfl⟩
    exact hull x ⟨hx,hy⟩
  · rintro x z ⟨hD,hx,hy,_⟩
    exact ⟨hD,hx,hy⟩
  · rintro x ⟨hD,hx,hy⟩
    exact ⟨2*(⌊x⌋ : ℤ),hD,hx,hy,rfl⟩

theorem partial_exclusion (D : ℝ → Prop) (x : ℝ) :
    ¬ ∃ z, partialParity D x z ∧ (1/2 : ℝ) ≤ z ∧ z ≤ 3/2 := by
  apply enclosure_window_exclusion (partial_sound D) (d := 2) (r := 0) (by norm_num)
  · intro z hz
    rw [hz.2.2.2]
    exact parity x
  · norm_num [parityEnclosure]

theorem hole_remains (x : ℝ) : ¬ ∃ z, partialParity (fun _ => False) x z := by
  rintro ⟨z,hz⟩
  exact hz.1

theorem composite_residue (x y : ℝ) :
    HasResidue 2 (-2) ((2*(⌊x⌋ : ℤ)+2*(⌈y⌉ : ℤ)) - 2) := by
  have hy : HasResidue 2 0 ((2 : ℝ)*(⌈y⌉ : ℤ)) := ⟨⌈y⌉, by push_cast; ring⟩
  have hc : HasResidue 2 2 (2 : ℝ) := ⟨0, by norm_num⟩
  simpa using residue_sub (residue_add (parity x) hy) hc

theorem negative_scale (x : ℝ) : HasResidue 2 0 (-3*(2*(⌊x⌋ : ℤ))) := by
  simpa using residue_scale (-3) (parity x)

#audit_namespace GeneralizedIntervalArithmetic.IntegerResidueChecks
end GeneralizedIntervalArithmetic.IntegerResidueChecks
