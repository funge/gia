import CutArithmetic
import AuditPolicy
namespace GeneralizedIntervalArithmetic.CutArithmeticChecks
open DedekindBoundary CutArithmetic

theorem strict_closed_operations :
    IsLUB (values (add (strict 1) (closed 2))) 3 ∧
    IsLUB (values (mul (strict 1) (closed 2))) 2 := by
  constructor
  · convert add_lub (strict_lub (by norm_num : (0:ℝ)<1))
      (closed_lub (by norm_num : (0:ℝ)<2)) using 1; norm_num
  · simpa using mul_lub (strict_lub (by norm_num : (0:ℝ)<1))
      (closed_lub (by norm_num : (0:ℝ)<2)) (fun _ h=>h.1) (fun _ h=>h.1)

theorem boundary_still_distinct :
    (2:ℚ)∉add (strict 1) (strict 1) ∧ (2:ℚ)∈add (closed 1) (closed 1) := by
  constructor
  · rintro ⟨a,ha,b,hb,h⟩
    have hab : (a:ℝ)+b=2 := by exact_mod_cast h
    linarith [ha.2,hb.2]
  · exact ⟨1,by norm_num [closed],1,by norm_num [closed],by norm_num⟩

theorem decoded_order_not_description_inclusion :
    sSup (values (closed 1)) ≤ sSup (values (strict 1)) ∧
    ¬ closed 1 ⊆ strict 1 := by
  constructor
  · rw [(same_supremum (by norm_num : (0:ℝ)<1)).1,
      (same_supremum (by norm_num : (0:ℝ)<1)).2]
  · intro h
    have hh := h (show (1:ℚ)∈closed 1 by norm_num [closed])
    norm_num [strict] at hh

theorem closed_zero_lub : IsLUB (values (closed 0)) 0 := by
  rw [zero_boundary.2]
  simp [values, isLUB_singleton]

theorem zero_arithmetic :
    IsLUB (values (add (closed 0) (strict 1))) 1 ∧
    IsLUB (values (mul (closed 0) (strict 1))) 0 := by
  constructor
  · simpa using add_lub closed_zero_lub (strict_lub (by norm_num : (0:ℝ)<1))
  · simpa using mul_lub closed_zero_lub (strict_lub (by norm_num : (0:ℝ)<1))
      (fun _ h=>h.1) (fun _ h=>h.1)

theorem empty_zero_is_not_additive_identity :
    add (strict 0) (closed 1) = ∅ ∧
    ¬ IsLUB (values (add (strict 0) (closed 1))) 1 := by
  have he : add (strict 0) (closed 1) = ∅ := by simp [add,zero_boundary.1]
  refine ⟨he,?_⟩
  intro h
  have hh : (1:ℝ)≤0 := h.2 (by simp [he,values,upperBounds])
  norm_num at hh

/-- The source's negative-cut warning uses all rational lower points, not Q≥0. -/
theorem negative_cut_lub : IsLUB (values {q:ℚ | q < -1}) (-1) := by
  classical
  constructor
  · rintro x ⟨q,hq,rfl⟩
    change q < -1 at hq
    change (q:ℝ) ≤ -1
    exact_mod_cast hq.le
  · intro u hu
    by_contra hn
    obtain ⟨q,huq,hq⟩ := exists_rat_btwn (lt_of_not_ge hn : u < -1)
    exact (not_le_of_gt huq) (hu ⟨q,by exact_mod_cast hq,rfl⟩)

theorem negative_product_not_cut :
    (∀ c∈({q:ℚ | q < -1}), ∀q:ℚ, q<c → q∈({q:ℚ | q < -1})) ∧
    ¬ Downward (mul {q:ℚ | q < -1} {q:ℚ | q < -1}) := by
  refine ⟨fun _ hc _ hq => hq.trans hc,?_⟩
  intro h
  have h4 : (4:ℚ)∈mul {q:ℚ | q < -1} {q:ℚ | q < -1} :=
    ⟨-2,by norm_num,-2,by norm_num,by norm_num⟩
  obtain ⟨a,ha,b,hb,hab⟩ := h 4 h4 0 (by norm_num) (by norm_num)
  change a < -1 at ha
  change b < -1 at hb
  have hp : 0<a*b := mul_pos_of_neg_of_neg (by linarith : a<0) (by linarith : b<0)
  dsimp at hab
  rw [hab] at hp
  exact lt_irrefl _ hp

end GeneralizedIntervalArithmetic.CutArithmeticChecks
#audit_namespace GeneralizedIntervalArithmetic.CutArithmeticChecks
