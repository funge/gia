import Mathlib.Data.Real.Hyperreal

/-! Source §2.6.1 positive infinitesimal, reusing the pinned mathlib model.
Independent of extended bounds, hardware, signed zero and general transfer. -/
namespace GeneralizedIntervalArithmetic.HyperrealInfinitesimal

theorem source_positive_infinitesimal :
    ∃ δ : Hyperreal, 0 < δ ∧ ∀ r : ℝ, 0 < r → δ < Hyperreal.ofReal r :=
  ⟨Hyperreal.epsilon, Hyperreal.epsilon_pos, Hyperreal.epsilon_lt_pos⟩

theorem epsilon_not_real : ¬ ∃ r : ℝ, Hyperreal.ofReal r = Hyperreal.epsilon := by
  rintro ⟨r,hr⟩
  have hp : (0 : Hyperreal) < Hyperreal.ofReal r := hr.symm ▸ Hyperreal.epsilon_pos
  have hpr : (0 : ℝ) < r := Hyperreal.coe_lt_coe.mp hp
  have h := Hyperreal.epsilon_lt_pos r hpr
  rw [hr] at h
  exact (lt_irrefl _) h

end GeneralizedIntervalArithmetic.HyperrealInfinitesimal
