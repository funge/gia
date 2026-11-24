import IntervalSetDenotation
import LinearIntervals
import Mathlib.Topology.Order.IntermediateValue

namespace GeneralizedIntervalArithmetic.IntervalCoefficientVariants

/-- Real choices inside finite rational closed coefficient intervals, at one t. -/
def values (P Q : QInterval) (t : ℝ) : Set ℝ :=
  IntervalSetDenotation.denote
    (fun pq : ℝ × ℝ => fun s => {pq.1 + pq.2*s})
    ({p | P.Contains p} ×ˢ {q | Q.Contains q}) t

def form (P Q : QInterval) : LinearInterval :=
  ⟨QAffine.ofCoefficients P.lo Q.lo, QAffine.ofCoefficients P.hi Q.hi,
   P.ordered, add_le_add P.ordered Q.ordered⟩

theorem mem_values (P Q : QInterval) (t z : ℝ) :
    z ∈ values P Q t ↔ ∃ p q : ℝ, P.Contains p ∧ Q.Contains q ∧ z = p+q*t := by
  constructor
  · rintro ⟨⟨p,q⟩,⟨hp,hq⟩,hz⟩
    exact ⟨p,q,hp,hq,Set.mem_singleton_iff.mp hz⟩
  · rintro ⟨p,q,hp,hq,rfl⟩
    exact ⟨(p,q),⟨hp,hq⟩,rfl⟩

/-- Exact pointwise correspondence, not merely enclosure. Attainment uses real
coefficient choices, and the coefficient intervals are closed and independent. -/
theorem exact_form (P Q : QInterval) {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    z ∈ values P Q t ↔ (form P Q).Contains t z := by
  rw [mem_values]
  change (∃ p q : ℝ, P.Contains p ∧ Q.Contains q ∧ z = p+q*t) ↔
    (QAffine.ofCoefficients P.lo Q.lo).value t ≤ z ∧
      z ≤ (QAffine.ofCoefficients P.hi Q.hi).value t
  rw [affine_ofCoefficients_value, affine_ofCoefficients_value]
  constructor
  · rintro ⟨p,q,hp,hq,rfl⟩
    exact ⟨add_le_add hp.1 (mul_le_mul_of_nonneg_right hq.1 ht),
      add_le_add hp.2 (mul_le_mul_of_nonneg_right hq.2 ht)⟩
  · intro hz
    let f : ℝ → ℝ := fun s =>
      ((1-s)*(P.lo:ℝ)+s*(P.hi:ℝ)) + ((1-s)*(Q.lo:ℝ)+s*(Q.hi:ℝ))*t
    have hf : ContinuousOn f (Set.Icc 0 1) := by fun_prop
    have hz' : z ∈ Set.Icc (f 0) (f 1) := by simpa [f] using hz
    obtain ⟨s,hs,hz⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hf hz'
    refine ⟨(1-s)*(P.lo:ℝ)+s*(P.hi:ℝ), (1-s)*(Q.lo:ℝ)+s*(Q.hi:ℝ), ?_, ?_, hz.symm⟩
    · constructor <;> dsimp [QInterval.Contains]
      · have hp : (P.lo:ℝ) ≤ P.hi := by exact_mod_cast P.ordered
        nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hp)]
      · have hp : (P.lo:ℝ) ≤ P.hi := by exact_mod_cast P.ordered
        nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hp)]
    · constructor <;> dsimp [QInterval.Contains]
      · have hq : (Q.lo:ℝ) ≤ Q.hi := by exact_mod_cast Q.ordered
        nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hq)]
      · have hq : (Q.lo:ℝ) ≤ Q.hi := by exact_mod_cast Q.ordered
        nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hq)]

/-- Literal equality of coefficient interval descriptions does not make the
represented real value a singleton. No two parameter values are identified. -/
theorem equal_description (P : QInterval) (t : ℝ) :
    values P P t = {z | ∃ p q : ℝ, P.Contains p ∧ P.Contains q ∧ z = p+q*t} := by
  ext z; exact mem_values P P t z

end GeneralizedIntervalArithmetic.IntervalCoefficientVariants
