import DiscreteDemotion
import Mathlib.Order.UpperLower.Basic
import AuditPolicy
namespace GeneralizedIntervalArithmetic.DiscreteDemotionChecks
open DiscreteDemotion

def coarse : Finset ℚ := {0,1}
def fine : Finset ℚ := {0,1/2,1}

theorem midpoint : down coarse ((1/2:ℝ):EReal) = 0 ∧ up coarse ((1/2:ℝ):EReal) = 1 := by
  constructor
  · apply down_eq
    · norm_num [mem_endpoints,coarse]
    · norm_cast; norm_num
    · intro v hv hx
      norm_num [mem_endpoints,coarse] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> norm_cast at *
      norm_num at *
  · apply up_eq
    · norm_num [mem_endpoints,coarse]
    · norm_cast; norm_num
    · intro v hv hx
      norm_num [mem_endpoints,coarse] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> norm_cast at *
      norm_num at *

theorem exact_representable : down coarse 1 = 1 ∧ up coarse 1 = 1 := by
  apply fixed
  norm_num [mem_endpoints,coarse]

theorem beyond_maximum : up coarse (2:ℝ) = ⊤ := by
  apply up_eq
  · simp [mem_endpoints]
  · exact le_top
  · intro v hv hx
    norm_num [mem_endpoints,coarse] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> norm_cast at *

theorem below_minimum : down coarse (-1:ℝ) = ⊥ := by
  apply down_eq
  · simp [mem_endpoints]
  · exact bot_le
  · intro v hv hx
    norm_num [mem_endpoints,coarse] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> norm_cast at *

theorem two_stage (x : EReal) :
    down coarse (down fine x) = down coarse x ∧ up coarse (up fine x) = up coarse x := by
  have h : coarse ⊆ fine := by intro q hq; simp [coarse] at hq; rcases hq with rfl|rfl <;> simp [fine]
  exact ⟨down_trans h x,up_trans h x⟩

theorem nonnested_conversion_can_lose_value :
    down coarse (down ({0,2}:Finset ℚ) 1) = 0 ∧ down coarse 1 = 1 := by
  have h : down ({0,2}:Finset ℚ) 1 = 0 := by
    apply down_eq
    · norm_num [mem_endpoints]
    · norm_num
    · intro v hv hx
      norm_num [mem_endpoints] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> norm_cast at *
  rw [h]
  exact ⟨(fixed (D:=coarse) (x:=0) (by norm_num [mem_endpoints,coarse])).1,
    exact_representable.1⟩

theorem empty_image (D : Finset ℚ) : hull D ∅ = ∅ := empty D

theorem full_real_image (D : Finset ℚ) : hull D Set.univ = Set.univ :=
  Set.Subset.antisymm (Set.subset_univ _) (sound _ _)

theorem unbounded_endpoints (D : Finset ℚ) :
    down D (ExtendedImageHull.lower Set.univ) = ⊥ ∧
    up D (ExtendedImageHull.upper Set.univ) = ⊤ := by
  exact ⟨unbounded_lower D (by simp),unbounded_upper D (by simp)⟩

theorem empty_family_rounding (x : ℝ) : down ∅ x = ⊥ ∧ up ∅ x = ⊤ := by
  constructor
  · apply down_eq (by simp [mem_endpoints]) bot_le
    intro v hv hx
    simp [mem_endpoints] at hv
    rcases hv with rfl|rfl <;> simp_all
  · apply up_eq (by simp [mem_endpoints]) le_top
    intro v hv hx
    simp [mem_endpoints] at hv
    rcases hv with rfl|rfl <;> simp_all

theorem halfline : hull coarse (Set.Ici (1/2:ℝ)) = Set.Ici (0:ℝ) := by
  have hl : ExtendedImageHull.lower (Set.Ici (1/2:ℝ)) = ((1/2:ℝ):EReal) := by
    rw [ExtendedImageHull.lower_finite Set.nonempty_Ici ⟨1/2,fun _ h => h⟩]
    simp
  have hu := unbounded_upper coarse (S:=Set.Ici (1/2:ℝ)) (not_bddAbove_Ici (1/2:ℝ))
  unfold hull
  rw [hl,midpoint.1,hu]
  ext x
  simp [ExtendedImageHull.interval]

set_option exponentiation.threshold 1100 in
theorem both_zero_words_fix_same_value :
    Binary64.decode 0 = Binary64.decode (2^63) ∧
    down binaryValues (0:ℝ) = 0 ∧ up binaryValues (0:ℝ) = 0 := by
  have hp : Binary64.decode 0 = some 0 := by norm_num [Binary64.decode,Binary64.exponent,Binary64.fraction,Binary64.sign]
  have hn : Binary64.decode (2^63) = some 0 := by norm_num [Binary64.decode,Binary64.exponent,Binary64.fraction,Binary64.sign]
  have h := decoded_fixed hp
  exact ⟨hp.trans hn.symm, by simpa using h⟩

theorem certified_pi_contains_demoted_image :
    ∀ x ∈ hull binaryValues {Real.pi}, HardwareAddition.Contains Binary64.real
      (⟨0x400921fb54442d18,0x400921fb54442d19⟩ : HardwareAddition.Bounds Binary64.Word) x := by
  apply word_certificate
  intro x hx
  have h : x=Real.pi := Set.mem_singleton_iff.mp hx
  subst x
  exact Binary64.pi_contains

theorem malformed_is_not_a_finite_value : Binary64.decode (2^64) = none :=
  Binary64.out_of_range _ le_rfl

end GeneralizedIntervalArithmetic.DiscreteDemotionChecks
#audit_namespace GeneralizedIntervalArithmetic.DiscreteDemotionChecks
