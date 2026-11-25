import NumberPromotion
import SequenceRepresentations
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-! Source-facing scalar correspondence for Tupper §§2.1–2.4.
Casts are exact embeddings, and partial graphs retain their domain guards. -/
namespace GeneralizedIntervalArithmetic.NumericFoundations

/-- The three explicitly printed homomorphism obligations in §2.2. -/
theorem integer_rational_embedding (a b : ℤ) :
    ((a+b:ℤ):ℚ) = (a:ℚ)+b ∧ ((a*b:ℤ):ℚ) = (a:ℚ)*b ∧
    (a>b ↔ (a:ℚ)>(b:ℚ)) := by norm_cast

theorem integer_rational_injective : Function.Injective (fun z : ℤ => (z:ℚ)) := by
  intro a b h
  change (a:ℚ)=(b:ℚ) at h
  exact_mod_cast h

theorem rational_real_embedding (a b : ℚ) :
    ((a+b:ℚ):ℝ) = (a:ℝ)+b ∧ ((a*b:ℚ):ℝ) = (a:ℝ)*b ∧
    (a>b ↔ (a:ℝ)>(b:ℝ)) := by norm_cast

theorem rational_real_injective : Function.Injective (fun q : ℚ => (q:ℝ)) := by
  intro a b h
  change (a:ℝ)=(b:ℝ) at h
  exact_mod_cast h

theorem rational_division_graph (a b c : ℚ) :
    (b≠0 ∧ c=a/b) ↔ PartialRealArithmetic.divRel (a:ℝ) b c := by
  simp only [PartialRealArithmetic.divRel,PartialRealArithmetic.divDefined,PartialRealArithmetic.div]
  norm_cast

/-- Integer division in the source is field division, not truncated Int.ediv. -/
theorem integer_division_not_closed : ¬∃ z : ℤ, (z:ℚ)=1/2 := by
  rintro ⟨z,hz⟩
  have h : (2:ℚ)*(z:ℚ)=1 := by linarith
  have hi : 2*z=1 := by exact_mod_cast h
  omega

theorem integer_alternative_distributivity_fails :
    ¬∀ x y z : ℤ, x+y*z=(x+y)*(x+z) := by
  intro h; have hh:=h 1 1 1; norm_num at hh

/-- Each real has a rational sequence representation. This is existence,
not a computable stream extractor or an accuracy rate. -/
theorem rational_sequence_exists (x : ℝ) :
    ∃ u : ℕ → ℚ, SequenceRepresentations.Represents u x := by
  obtain ⟨u,_,h⟩ := Real.exists_seq_rat_strictMono_tendsto x
  exact ⟨u,h.2⟩

theorem rational_constant_representation (q : ℚ) :
    SequenceRepresentations.Represents (fun _ => q) (q:ℝ) :=
  SequenceRepresentations.constant q

/-- Relational nonnegative square root, exactly the already-used partial graph. -/
theorem real_root_graph (x z : ℝ) :
    SqrtValues (fun (_ : Unit) (_ : Unit) y => y=x) () () z ↔
      0≤z ∧ z^2=x := by
  constructor
  · rintro ⟨y,rfl,hx,rfl⟩
    exact ⟨Real.sqrt_nonneg _,Real.sq_sqrt hx⟩
  · rintro ⟨hz,hx⟩
    have h0 : 0≤x := by rw [←hx]; exact sq_nonneg z
    exact ⟨x,rfl,h0,((Real.sqrt_eq_iff_eq_sq h0 hz).2 hx.symm).symm⟩

theorem real_root_domain (x : ℝ) :
    (∃ z : ℝ, 0≤z ∧ z^2=x) ↔ 0≤x := by
  constructor
  · rintro ⟨z,_,rfl⟩; exact sq_nonneg z
  · intro hx; exact ⟨Real.sqrt x,Real.sqrt_nonneg _,Real.sq_sqrt hx⟩

theorem root_observation_graph (x z : ℝ) :
    ExceptionalComparisons.sqrtObservation (.finite x) = some (.finite z) ↔
      0≤z ∧ z^2=x :=
  (ExceptionalComparisons.sqrt_finite_agreement x z).trans (real_root_graph x z)

theorem no_rational_root_two : ¬∃ q : ℚ, q^2=2 := by
  rintro ⟨q,hq⟩
  have hr : (q:ℝ)^2=2 := by exact_mod_cast hq
  have he : Real.sqrt 2 = ((|q|:ℚ):ℝ) := by
    rw [←hr,Real.sqrt_sq_eq_abs]; simp
  exact irrational_sqrt_two ⟨|q|,he.symm⟩

theorem no_rational_root_negative_one : ¬∃ q : ℚ, q^2 = -1 := by
  rintro ⟨q,hq⟩; nlinarith [sq_nonneg q]

theorem no_total_rational_root : ¬∃ f : ℚ → ℚ, ∀ x, (f x)^2=x := by
  rintro ⟨f,h⟩; exact no_rational_root_two ⟨f 2,h 2⟩

theorem real_complex_embedding (a b : ℝ) :
    ((a+b:ℝ):ℂ) = (a:ℂ)+b ∧ ((a*b:ℝ):ℂ) = (a:ℂ)*b := by simp

theorem real_complex_injective : Function.Injective (fun x : ℝ => (x:ℂ)) :=
  Complex.ofReal_injective

theorem promotion_chain (z : ℤ) : (((z:ℚ):ℝ):ℂ) = (z:ℂ) := by norm_cast

theorem complex_division_graph (a b c : ℝ) :
    PartialRealArithmetic.divRel a b c ↔ (b:ℂ)≠0 ∧ (c:ℂ)=(a:ℂ)/(b:ℂ) := by
  simp only [PartialRealArithmetic.divRel,PartialRealArithmetic.divDefined,PartialRealArithmetic.div]
  norm_cast

/-- An actual total square-root choice from pinned mathlib's complex power.
No claim that it restricts to the principal real root on negative inputs. -/
noncomputable def complexRoot (z : ℂ) : ℂ := z ^ ((2:ℂ)⁻¹)

theorem complex_root_square (z : ℂ) : (complexRoot z)^2=z :=
  Complex.cpow_nat_inv_pow z (by norm_num)

theorem complex_root_total (z : ℂ) : ∃ w : ℂ, w^2=z := ⟨complexRoot z,complex_root_square z⟩

theorem complex_negative_root : Complex.I^2 = (-1:ℂ) := Complex.I_sq

/-- Precise order obstruction, not the claim that no order can be put on a set. -/
theorem no_complex_ordered_ring [LinearOrder ℂ] [IsStrictOrderedRing ℂ] : False := by
  have h := sq_nonneg Complex.I
  rw [Complex.I_sq] at h
  have hn : (-1:ℂ)<0 := neg_neg_of_pos zero_lt_one
  exact (not_le_of_gt hn) h

end GeneralizedIntervalArithmetic.NumericFoundations
