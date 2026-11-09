import CoverPresence
import ThresholdCertification
import GuardedSimplification
import AuditPolicy

/- Fresh core-only client: branch-local certificates and independent controls. -/
namespace GeneralizedIntervalArithmetic.ThresholdCertificateChecks

def X : LinearInterval := .exact ⟨0,1⟩
def Y : LinearInterval := .exact ⟨0,0⟩
def a : Expr := .div (.const 1) (.sub .x (.const 1))
def b : Expr := .div (.const 1) .x
def expression : ConditionalExpr := .iteLt .x (1/2) (.leaf a) (.leaf b)
noncomputable def representative (t : ℝ) : ℝ := if t < (1/2:ℝ) then 1/(t-1) else 1/t

theorem globally_unknown : (evalConditionalCover X Y expression).isNone := by decide +kernel

theorem actual_value (t : ℝ) : ConditionalValue t 0 expression (representative t) := by
  have hc : Value t 0 (.const 1) (1:ℝ) := by
    simpa using (Value.const (x := t) (y := (0:ℝ)) (1:ℚ))
  by_cases h : t < (1/2:ℝ)
  · simp only [representative,if_pos h]
    apply ConditionalValue.yes Value.x (by simpa using h)
    apply ConditionalValue.leaf
    exact Value.div hc (Value.sub Value.x hc) (by linarith)
  · simp only [representative,if_neg h]
    apply ConditionalValue.no Value.x (by simpa using le_of_not_gt h)
    apply ConditionalValue.leaf
    exact Value.div hc Value.x (by linarith [le_of_not_gt h])

theorem all_points_defined (t : ℝ) : ∃ z, ConditionalValue t 0 expression z :=
  ⟨representative t,actual_value t⟩

theorem actual_zero_absent (t : ℝ) : ¬ ConditionalValue t 0 expression 0 := by
  intro hz
  have he := conditional_value_unique (actual_value t) hz
  unfold representative at he
  split at he
  · exact div_ne_zero (by norm_num) (by linarith) he
  · rename_i hn
    exact div_ne_zero (by norm_num) (by linarith [le_of_not_gt hn]) he

def left : ParameterCell := ⟨⟨0,1/2,by norm_num⟩,le_rfl,by norm_num⟩
def right : ParameterCell := ⟨⟨1/2,1,by norm_num⟩,by norm_num,le_rfl⟩

theorem left_branch_success :
    (evalGuarded (X.reparam left) (Y.reparam left) a).isSome := by decide +kernel

theorem right_branch_success :
    (evalGuarded (X.reparam right) (Y.reparam right) b).isSome := by decide +kernel

def leftRange := (evalGuarded (X.reparam left) (Y.reparam left) a).get left_branch_success
def rightRange := (evalGuarded (X.reparam right) (Y.reparam right) b).get right_branch_success

theorem branch_ranges_exclude_zero : leftRange.hull.AwayZero ∧ rightRange.hull.AwayZero := by
  decide +kernel

/-- Endpoint signs alone cannot certify a root through this conditional. -/
theorem opposite_endpoints_without_root :
    representative 0 < 0 ∧ 0 < representative 1 ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, ¬ ConditionalValue t 0 expression 0 := by
  refine ⟨?_,?_,fun t _ => actual_zero_absent t⟩ <;> norm_num [representative]

theorem boundary_uses_false_branch : ConditionalValue (1/2) 0 expression 2 := by
  convert actual_value (1/2) using 1
  norm_num [representative]

def boundaryHole : ConditionalExpr := .iteLt .x (1/2) (.leaf a)
  (.leaf (.div (.const 1) (.sub .x (.const (1/2)))))

theorem boundary_hole_undefined : ¬ ∃ z, ConditionalValue (1/2) 0 boundaryHole z := by
  rintro ⟨z,hz⟩
  cases hz with
  | yes hg hlt _ =>
    have he := value_eq_realValue hg
    norm_num [Expr.realValue] at he
    subst_vars
    norm_num at hlt
  | no _ _ hb =>
    cases hb with
    | leaf hv =>
      cases hv with
      | div _ hd hn =>
        have he := value_eq_realValue hd
        norm_num [Expr.realValue] at he
        exact hn he

private theorem input_x (t : ℝ) : X.Contains t t := by
  simp [X,LinearInterval.Contains,LinearInterval.exact,QAffine.value]
private theorem input_y (t : ℝ) : Y.Contains t 0 := by
  simp [Y,LinearInterval.Contains,LinearInterval.exact,QAffine.value]

theorem certified :
    evalThresholdBranches X Y (1/2) (by norm_num) (.leaf a) (.leaf b) =
      some ([leftRange],[rightRange]) := by
  unfold evalThresholdBranches
  change (do
    let A ← (evalGuarded (X.reparam left) (Y.reparam left) a).map (fun I => [I])
    let B ← (evalGuarded (X.reparam right) (Y.reparam right) b).map (fun I => [I])
    pure (A,B)) = some ([leftRange],[rightRange])
  rw [← Option.some_get left_branch_success,← Option.some_get right_branch_success]
  rfl

theorem certified_defined {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃ z, ConditionalValue t 0 expression z :=
  threshold_branches_defined certified ht (input_x t) (input_y t) Value.x

theorem certified_no_zero {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ¬ ConditionalValue t 0 expression 0 := by
  apply threshold_branches_exclude_zero certified _ _ ht (input_x t) (input_y t) Value.x
  · intro I hi
    have he := List.mem_singleton.mp hi
    subst I
    exact branch_ranges_exclude_zero.1
  · intro I hi
    have he := List.mem_singleton.mp hi
    subst I
    exact branch_ranges_exclude_zero.2

theorem boundary_enclosed_on_right :
    ∃ s ∈ Set.Icc (0:ℝ) 1, (ParameterCell.thresholdRight (1/2) (by norm_num)).map s = 1/2 ∧
      ∃ I ∈ [rightRange], I.Contains s 2 := by
  rcases threshold_branches_enclose certified (by norm_num) (input_x (1/2)) (input_y (1/2))
      Value.x boundary_uses_false_branch with h | h
  · norm_num at h
  · exact h.2

/-- End-to-end exclusion despite opposite endpoint signs; no continuity premise. -/
theorem certified_jump_without_root : representative 0 < 0 ∧ 0 < representative 1 ∧
    ∀ t ∈ Set.Icc (0:ℝ) 1, ¬ ConditionalValue t 0 expression 0 := by
  refine ⟨?_,?_,fun _ ht => certified_no_zero ht⟩ <;> norm_num [representative]

theorem active_boundary_pole_unknown :
    (evalThresholdBranches X Y (1/2) (by norm_num) (.leaf a)
      (.leaf (.div (.const 1) (.sub .x (.const (1/2)))))).isNone := by decide +kernel

/-- A singularity at the inactive true-branch boundary still defeats the closed
cell check. This is incompleteness, not actual undefinedness. -/
def inactiveBoundary : ConditionalExpr := .iteLt .x (1/2)
  (.leaf (.div (.const 1) (.sub .x (.const (1/2))))) (.leaf (.const 0))

theorem inactive_boundary_unknown :
    (evalThresholdBranches X Y (1/2) (by norm_num)
      (.leaf (.div (.const 1) (.sub .x (.const (1/2))))) (.leaf (.const 0))).isNone := by
  decide +kernel

theorem inactive_boundary_defined (t : ℝ) : ∃ z, ConditionalValue t 0 inactiveBoundary z := by
  by_cases h : t < (1/2:ℝ)
  · refine ⟨1/(t-(1/2:ℝ)),ConditionalValue.yes Value.x (by simpa using h) ?_⟩
    apply ConditionalValue.leaf
    have hc : Value t 0 (.const 1) (1:ℝ) := by simpa using
      (Value.const (x := t) (y := (0:ℝ)) (1:ℚ))
    have hh : Value t 0 (.const (1/2)) (1/2:ℝ) := by simpa using
      (Value.const (x := t) (y := (0:ℝ)) (1/2:ℚ))
    exact Value.div hc (Value.sub Value.x hh) (by linarith)
  · refine ⟨0,ConditionalValue.no Value.x (by simpa using le_of_not_gt h) ?_⟩
    apply ConditionalValue.leaf
    simpa using (Value.const (x := t) (y := (0:ℝ)) (0:ℚ))

/-- Construct actual values below any proposed lower bound, while staying
strictly inside the active branch. The boundary itself is not used. -/
theorem inactive_branch_unbounded (l : ℝ) :
    ∃ t ∈ Set.Ico (0:ℝ) (1/2), ∃ z, ConditionalValue t 0 inactiveBoundary z ∧ z < l := by
  let d := 2 + |l|
  have hd : 0 < d := by dsimp [d]; positivity
  have hs : 0 < 1/d := one_div_pos.mpr hd
  have hsle : 1/d ≤ (1/2:ℝ) := by
    apply (div_le_iff₀ hd).mpr
    dsimp [d]
    linarith [abs_nonneg l]
  let t := (1/2:ℝ) - 1/d
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have htq : t < (1/2:ℝ) := by dsimp [t]; linarith
  have htden : t - (1/2:ℝ) = -(1/d) := by dsimp [t]; ring
  have he : 1/(t-(1/2:ℝ)) = -d := by rw [htden]; simp [one_div]
  refine ⟨t,⟨ht0,htq⟩,-d,?_,?_⟩
  · rw [← he]
    apply ConditionalValue.yes Value.x (by simpa using htq)
    apply ConditionalValue.leaf
    have hc : Value t 0 (.const 1) (1:ℝ) := by simpa using
      (Value.const (x := t) (y := (0:ℝ)) (1:ℚ))
    have hh : Value t 0 (.const (1/2)) (1/2:ℝ) := by simpa using
      (Value.const (x := t) (y := (0:ℝ)) (1/2:ℚ))
    exact Value.div hc (Value.sub Value.x hh) (by linarith)
  · dsimp [d]
    linarith [neg_abs_le l]

theorem inactive_boundary_no_finite_cover (C : FiniteLinearCover) :
    ¬ C.Covers (fun t z => ConditionalValue t 0 inactiveBoundary z) := by
  apply no_finite_cover_of_unbounded_below _ C
  intro l
  obtain ⟨t,ht,z,hz,hl⟩ := inactive_branch_unbounded l
  exact ⟨t,⟨ht.1,by linarith [ht.2]⟩,z,hz,hl⟩

/-- Moving to the left cell's local parameter does not remove the unbounded
values approaching its inactive endpoint. -/
theorem inactive_left_no_finite_cover (C : FiniteLinearCover) :
    ¬ C.Covers (fun s z => ConditionalValue (left.map s) 0 inactiveBoundary z) := by
  apply no_finite_cover_of_unbounded_below _ C
  intro l
  obtain ⟨t,ht,z,hz,hl⟩ := inactive_branch_unbounded l
  have hm : left.interval.Contains t := by
    simpa [left,QInterval.Contains] using And.intro ht.1 ht.2.le
  obtain ⟨s,hs,he⟩ := parameter_map_onto left hm
  exact ⟨s,hs,z,he.symm ▸ hz,hl⟩

/-- A distinct failure mode: cancellation leaves a bounded active value, but
must not silently assign a value to division by zero at the inactive boundary. -/
def removableBoundary : ConditionalExpr := .iteLt .x (1/2)
  (.leaf (.div (.sub .x (.const (1/2))) (.sub .x (.const (1/2))))) (.leaf (.const 1))

theorem removable_boundary_unknown :
    (evalThresholdBranches X Y (1/2) (by norm_num)
      (.leaf (.div (.sub .x (.const (1/2))) (.sub .x (.const (1/2)))))
      (.leaf (.const 1))).isNone := by decide +kernel

theorem removable_actual_one (t : ℝ) : ConditionalValue t 0 removableBoundary 1 := by
  by_cases h : t < (1/2:ℝ)
  · apply ConditionalValue.yes Value.x (by simpa using h)
    apply ConditionalValue.leaf
    have hh : Value t 0 (.const (1/2)) (1/2:ℝ) := by simpa using
      (Value.const (x := t) (y := (0:ℝ)) (1/2:ℚ))
    have hn : t - (1/2:ℝ) ≠ 0 := by linarith
    have hv := Value.div (Value.sub Value.x hh) (Value.sub Value.x hh) hn
    rw [div_self hn] at hv
    exact hv
  · apply ConditionalValue.no Value.x (by simpa using le_of_not_gt h)
    apply ConditionalValue.leaf
    simpa using (Value.const (x := t) (y := (0:ℝ)) (1:ℚ))

theorem removable_has_finite_cover :
    FiniteLinearCover.Covers [LinearInterval.exact ⟨1,1⟩]
      (fun t z => ConditionalValue t 0 removableBoundary z) := by
  apply cover_singleton
  intro t _ z hz
  have he := conditional_value_unique hz (removable_actual_one t)
  subst z
  simp [LinearInterval.Contains,LinearInterval.exact,QAffine.value]

def badGuard : Expr := .div (.const 1) (.const 0)

theorem branch_checks_do_not_check_guard :
    (evalThresholdBranches X Y (1/2) (by norm_num) (.leaf (.const 1)) (.leaf (.const 2))).isSome := by
  decide +kernel

theorem bad_guard_no_value (t : ℝ) : ¬ ∃ z, Value t 0 badGuard z := by
  rintro ⟨z,hz⟩
  cases hz with
  | div _ hb hn =>
    cases hb
    norm_num at hn

theorem bad_guard_conditional_undefined (t : ℝ) :
    ¬ ∃ z, ConditionalValue t 0 (.iteLt badGuard (1/2) (.leaf (.const 1)) (.leaf (.const 2))) z := by
  rintro ⟨z,hz⟩
  cases hz with
  | yes hg _ _ => exact bad_guard_no_value t ⟨_,hg⟩
  | no hg _ _ => exact bad_guard_no_value t ⟨_,hg⟩

/-- A genuine affine result on the left cell needs local parameter 1/2 to
represent global parameter 1/4. Using the global parameter directly is wrong. -/
theorem local_parameter_cannot_be_flattened :
    (X.reparam left).Contains (1/2) (1/4) ∧
    ¬ (X.reparam left).Contains (1/4) (1/4) := by
  norm_num [X,left,LinearInterval.reparam,QAffine.reparam,
    LinearInterval.Contains,LinearInterval.exact,QAffine.value]

theorem affine_left_result :
    evalConditionalCover (X.reparam left) (Y.reparam left) (.leaf .x) =
      some [X.reparam left] := rfl

/-- Degenerate endpoint cells remain supported, without dropping either check. -/
theorem endpoint_thresholds_supported :
    (evalThresholdBranches X Y 0 (by norm_num) (.leaf (.const 1)) (.leaf (.const 2))).isSome ∧
    (evalThresholdBranches X Y 1 (by norm_num) (.leaf (.const 1)) (.leaf (.const 2))).isSome := by
  decide +kernel

namespace Cancellation

def rewritten : ConditionalExpr := .iteLt .x (1/2) (.leaf (.const 1)) (.leaf (.const 1))

theorem exact_semantics (x y z : ℝ) :
    ConditionalValue x y removableBoundary z ↔ ConditionalValue x y rewritten z :=
  conditional_threshold_self_div_iff .x (1/2) (.leaf (.const 1)) x y z

theorem rewritten_success : (evalConditionalCover X Y rewritten).isSome := by decide +kernel

def result := (evalConditionalCover X Y rewritten).get rewritten_success

theorem coefficients : result.map (fun I => (I.lower,I.upper)) =
    [(⟨1,1⟩,⟨1,1⟩),(⟨1,1⟩,⟨1,1⟩)] := by decide +kernel

def punctured : DomainBounds ℝ :=
  ⟨fun t => t ≠ (1/4:ℝ),fun t => t ≠ (1/4:ℝ),fun _ h => h⟩
def full : DomainBounds ℝ := ⟨fun _ => True,fun _ => True,fun _ h => h⟩
def EnvX (t z : ℝ) := t ∈ Set.Icc (0:ℝ) 1 ∧ t ≠ (1/4:ℝ) ∧ z = t
def EnvY (t z : ℝ) := t ∈ Set.Icc (0:ℝ) 1 ∧ z = 0

theorem x_sound : (X.onDomain punctured).Sound EnvX := by
  refine ⟨?_,fun _ _ h => ⟨h.1,h.2.1⟩,fun t h => ⟨t,h.1,h.2,rfl⟩⟩
  rintro t z ⟨_,_,rfl⟩
  exact input_x _

theorem y_sound : (Y.onDomain full).Sound EnvY := by
  refine ⟨?_,fun _ _ h => ⟨h.1,trivial⟩,fun t h => ⟨0,h.1,rfl⟩⟩
  rintro t z ⟨_,rfl⟩
  exact input_y t

/-- The existing evaluator certifies the original expression's partial relation
through the exact rewrite, not merely the simplified expression's range. -/
theorem original_contract : result.SoundOn (punctured.inter full)
    (ConditionalExpressionValues EnvX EnvY removableBoundary) :=
  evalConditionalCover_equivalent_sound exact_semantics x_sound y_sound
    (Option.some_get rewritten_success).symm

theorem external_hole_preserved :
    ¬ ∃ z, ConditionalExpressionValues EnvX EnvY removableBoundary (1/4) z := by
  apply cover_domain_absent original_contract
  simp [DomainBounds.inter,punctured]

theorem original_endpoint_exists :
    ∃ z, ConditionalExpressionValues EnvX EnvY removableBoundary 0 z := by
  apply cover_domain_definite original_contract (by norm_num)
  norm_num [DomainBounds.inter,punctured,full]

theorem original_no_zero {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ¬ ConditionalExpressionValues EnvX EnvY removableBoundary t 0 := by
  apply cover_excludes_zero (cover_soundOn_covers original_contract) _ ht
  intro I hi
  have ha : result.all (fun J => decide J.hull.AwayZero) = true := by decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp ha) I hi)

/-- A rewrite must retain undefinedness of the guard itself. -/
theorem undefined_guard_preserved (t : ℝ) :
    ¬ ∃ z, ConditionalValue t 0 (.iteLt badGuard (1/2)
      (.leaf (.div (.sub badGuard (.const (1/2))) (.sub badGuard (.const (1/2)))))
      (.leaf (.const 2))) z := by
  rintro ⟨z,hz⟩
  exact bad_guard_conditional_undefined t ⟨z,
    (conditional_threshold_self_div_iff badGuard (1/2) (.leaf (.const 2)) t 0 z).mp hz⟩

theorem false_pole_unknown :
    (evalConditionalCover X Y (.iteLt .x (1/2) (.leaf (.const 1)) (.leaf badGuard))).isNone := by
  decide +kernel

theorem false_pole_at_equality :
    ¬ ∃ z, ConditionalValue (1/2) 0 (.iteLt .x (1/2) (.leaf (.const 1)) (.leaf badGuard)) z := by
  rintro ⟨z,hz⟩
  cases hz with
  | yes hg hlt _ =>
    have he := value_eq_realValue hg
    norm_num [Expr.realValue] at he
    subst_vars
    norm_num at hlt
  | no _ _ hb => exact bad_guard_no_value (1/2) ⟨z,conditional_leaf_iff.mp hb⟩

theorem unguarded_cancellation_invalid : ¬ ∃ z, Value 0 0 (.div .x .x) z := by
  rintro ⟨z,h⟩
  cases h with
  | div _ hb hn =>
    cases hb
    exact hn rfl

end Cancellation

end GeneralizedIntervalArithmetic.ThresholdCertificateChecks
#audit_namespace GeneralizedIntervalArithmetic.ThresholdCertificateChecks
