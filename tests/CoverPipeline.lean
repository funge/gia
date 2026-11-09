import CoverRestriction
import CoverArithmetic
import AuditPolicy

/- Independent client of the public core APIs; no milestone example imports. -/
namespace GeneralizedIntervalArithmetic.CoverPipelineChecks

def X : LinearInterval := .exact ⟨0,1⟩
def Y : LinearInterval := .exact ⟨0,0⟩
def positive : Expr := .add .x (.const 2)
def choice : ConditionalExpr := .iteLt .x (1/4)
  (.leaf (.sub (.const 0) positive)) (.leaf positive)
def cell : ParameterCell := ⟨⟨1/4,3/4,by norm_num⟩,by norm_num,by norm_num⟩
def punctured : DomainBounds ℝ :=
  ⟨fun t => t ≠ (1/2:ℝ),fun t => t ≠ (1/2:ℝ),fun _ h => h⟩
def everywhere : DomainBounds ℝ := ⟨fun _ => True,fun _ => True,fun _ h => h⟩
def A (t z : ℝ) := t ∈ Set.Icc (0:ℝ) 1 ∧ t ≠ (1/2:ℝ) ∧ z = t
def B (t z : ℝ) := t ∈ Set.Icc (0:ℝ) 1 ∧ z = 0

theorem x_contract : (X.onDomain punctured).Sound A := by
  refine ⟨?_,fun _ _ h => ⟨h.1,h.2.1⟩,fun t h => ⟨t,h.1,h.2,rfl⟩⟩
  rintro t z ⟨_,_,hz⟩
  subst z
  change X.Contains t t
  simp [X,LinearInterval.Contains,LinearInterval.exact,QAffine.value]

theorem y_contract : (Y.onDomain everywhere).Sound B := by
  refine ⟨?_,fun _ _ h => ⟨h.1,trivial⟩,fun t h => ⟨0,h.1,rfl⟩⟩
  rintro t z ⟨_,rfl⟩
  change Y.Contains t 0
  simp [Y,LinearInterval.Contains,LinearInterval.exact,QAffine.value]

theorem local_success : (evalConditionalCover (X.reparam cell) (Y.reparam cell) choice).isSome := by
  decide +kernel

def localResult : FiniteLinearCover :=
  (evalConditionalCover (X.reparam cell) (Y.reparam cell) choice).get local_success

theorem local_coefficients : localResult.map (fun I => (I.lower,I.upper)) =
    [(⟨9/4,11/4⟩,⟨9/4,11/4⟩)] := by decide +kernel

def LocalValues (s z : ℝ) := s ∈ Set.Icc (0:ℝ) 1 ∧
  ConditionalExpressionValues A B choice (cell.map s) z

def localDomain := (cell.pullDomain punctured).inter (cell.pullDomain everywhere)

theorem local_contract : localResult.SoundOn localDomain LocalValues :=
  evalConditionalCover_reparam_relational_sound cell x_contract y_contract
    (Option.some_get local_success).symm

theorem local_limit : localResult.limit 1 = some localResult :=
  cover_limit_unchanged (by decide +kernel)

theorem limited_contract : localResult.SoundOn localDomain LocalValues :=
  cover_limit_domain_sound local_contract local_limit

theorem reciprocal_success : localResult.recip?.isSome := by decide +kernel

def result : FiniteLinearCover := localResult.recip?.get reciprocal_success

def pipeline := (evalConditionalCover (X.reparam cell) (Y.reparam cell) choice).bind
  (fun F => (F.limit 1).bind FiniteLinearCover.recip?)

theorem pipeline_result : pipeline = some result := by
  unfold pipeline
  rw [← Option.some_get local_success]
  change (localResult.limit 1).bind FiniteLinearCover.recip? = some result
  rw [local_limit]
  exact (Option.some_get reciprocal_success).symm

theorem result_coefficients : result.map (fun I => (I.lower,I.upper)) =
    [(⟨4/11,4/11⟩,⟨4/9,4/9⟩)] := by decide +kernel

def FinalValues := QuotientValues (fun _ z => z = 1) LocalValues

theorem final_contract : result.SoundOn localDomain FinalValues :=
  cover_recip_domain_sound limited_contract (Option.some_get reciprocal_success).symm

theorem interior_hole_preserved : ¬ ∃ z, FinalValues (1/2) z := by
  apply cover_domain_absent final_contract
  intro h
  have hn := h.1
  norm_num [ParameterCell.pullDomain,punctured,cell,ParameterCell.map] at hn

theorem both_endpoints_defined : (∃ z, FinalValues 0 z) ∧ (∃ z, FinalValues 1 z) := by
  constructor
  · apply cover_domain_definite final_contract (by norm_num)
    change cell.map 0 ≠ (1/2:ℝ) ∧ True
    norm_num [cell,ParameterCell.map]
  · apply cover_domain_definite final_contract (by norm_num)
    change cell.map 1 ≠ (1/2:ℝ) ∧ True
    norm_num [cell,ParameterCell.map]

theorem excludes_zero {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) : ¬ FinalValues s 0 := by
  apply cover_excludes_zero (cover_soundOn_covers final_contract) _ hs
  intro I hi
  have ha : result.all (fun J => decide J.hull.AwayZero) = true := by decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp ha) I hi)

/-- A coarser analysis remains unknown even though the restricted pipeline succeeds. -/
theorem global_limit_one_unknown :
    ((evalConditionalCover X Y choice).bind
      (fun F => (F.limit 1).bind FiniteLinearCover.recip?)).isNone := by decide +kernel

theorem global_limit_two_succeeds :
    ((evalConditionalCover X Y choice).bind
      (fun F => (F.limit 2).bind FiniteLinearCover.recip?)).isSome := by decide +kernel

theorem zero_capacity_unknown :
    ((evalConditionalCover (X.reparam cell) (Y.reparam cell) choice).bind
      (FiniteLinearCover.limit 0)).isNone := by decide +kernel

/-- Defined representative values cannot supply the missing environment membership. -/
theorem expression_defined_at_hole : ConditionalValue (1/2) 0 choice (5/2) := by
  apply ConditionalValue.no Value.x (by norm_num)
  apply ConditionalValue.leaf
  convert (Value.add (Value.x (x := (1/2:ℝ)) (y := (0:ℝ))) (Value.const 2)) using 1
  norm_num [positive]

/-- Compose the restricted conditional range with its guarded reciprocal. -/
def products := localResult.mul result
def ProductRelation := ProductValues LocalValues FinalValues

theorem product_contract : products.SoundOn (localDomain.inter localDomain) ProductRelation :=
  cover_mul_domain_sound local_contract final_contract

theorem product_hole_preserved : ¬ ∃ z, ProductRelation (1/2) z := by
  rintro ⟨z,x,y,_,hy,_⟩
  exact interior_hole_preserved ⟨y,hy⟩

theorem product_excludes_zero {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    ¬ ProductRelation s 0 := by
  apply cover_excludes_zero (cover_soundOn_covers product_contract) _ hs
  intro I hi
  have ha : products.all (fun J => decide J.hull.AwayZero) = true := by decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp ha) I hi)

/-- Choose the same actual denominator to exhibit one actual product. The
product enclosure itself need not record that witness correlation. -/
theorem actual_product_one {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1)
    (hd : localDomain.definite s) : ProductRelation s 1 := by
  obtain ⟨y,hy⟩ := cover_domain_definite local_contract hs hd
  obtain ⟨I,hi,hI⟩ := local_contract.1 s y hy
  obtain ⟨J,_,hj⟩ := cover_recip_member (Option.some_get reciprocal_success).symm hi
  have hn := linear_recip_nonzero hj hs hI
  refine ⟨y,1/y,hy,⟨1,y,rfl,hy,hn,rfl⟩,?_⟩
  field_simp

theorem product_one_at_endpoint : ProductRelation 0 1 := by
  apply actual_product_one (by norm_num)
  change cell.map 0 ≠ (1/2:ℝ) ∧ True
  norm_num [cell,ParameterCell.map]

theorem product_coalesce_contract :
    (products.coalesce).SoundOn (localDomain.inter localDomain) ProductRelation :=
  cover_coalesce_domain_sound product_contract

def squaredReciprocal := localResult.square.recip?
theorem squared_reciprocal_success : squaredReciprocal.isSome := by decide +kernel
def squaredResult : FiniteLinearCover := squaredReciprocal.get squared_reciprocal_success

def SquaredReciprocalValues := QuotientValues (fun _ z => z = 1) (SquareValues LocalValues)

theorem squared_reciprocal_contract : squaredResult.SoundOn localDomain SquaredReciprocalValues :=
  cover_recip_domain_sound (cover_square_domain_sound local_contract)
    (Option.some_get squared_reciprocal_success).symm

theorem squared_reciprocal_hole : ¬ ∃ z, SquaredReciprocalValues (1/2) z := by
  apply cover_domain_absent squared_reciprocal_contract
  intro h
  have hn := h.1
  norm_num [ParameterCell.pullDomain,punctured,cell,ParameterCell.map] at hn

theorem squared_reciprocal_endpoint : ∃ z, SquaredReciprocalValues 0 z := by
  apply cover_domain_definite squared_reciprocal_contract (by norm_num)
  change cell.map 0 ≠ (1/2:ℝ) ∧ True
  norm_num [cell,ParameterCell.map]

theorem squared_reciprocal_no_zero {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    ¬ SquaredReciprocalValues s 0 := by
  apply cover_excludes_zero (cover_soundOn_covers squared_reciprocal_contract) _ hs
  intro I hi
  have ha : squaredResult.all (fun J => decide J.hull.AwayZero) = true := by decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp ha) I hi)

namespace Multivalued

def neg : LinearInterval := .exact ⟨-1,-1⟩
def pos : LinearInterval := .exact ⟨1,1⟩
def signs : FiniteLinearCover := [neg,pos]
def Values (t z : ℝ) := t ∈ Set.Icc (0:ℝ) 1 ∧ (z = -1 ∨ z = 1)

theorem contract : signs.SoundOn everywhere Values := by
  refine ⟨?_,fun _ _ h => ⟨h.1,trivial⟩,fun t h => ⟨1,h.1,Or.inr rfl⟩⟩
  rintro t z ⟨_,hz⟩
  rcases hz with rfl | rfl
  · exact ⟨neg,by simp [signs],by
      simp [neg,LinearInterval.Contains,LinearInterval.exact,QAffine.value]⟩
  · exact ⟨pos,by simp [signs],by
      simp [pos,LinearInterval.Contains,LinearInterval.exact,QAffine.value]⟩

theorem four_pairs : (signs.mul signs).length = 4 := by decide +kernel

theorem products_sound : (signs.mul signs).SoundOn (everywhere.inter everywhere)
    (ProductValues Values Values) := cover_mul_domain_sound contract contract

theorem mixed_product_actual : ProductValues Values Values 0 (-1) := by
  exact ⟨-1,1,⟨by norm_num,Or.inl rfl⟩,⟨by norm_num,Or.inr rfl⟩,by norm_num⟩

/-- Pairing corresponding list positions drops the mixed-sign products. -/
theorem zipped_products_unsound :
    ¬ FiniteLinearCover.Covers [neg.mul neg,pos.mul pos] (ProductValues Values Values) := by
  intro h
  obtain ⟨I,hi,hz⟩ := h 0 (by norm_num) (-1) mixed_product_actual
  rcases List.mem_cons.mp hi with rfl | hi
  · norm_num [neg,LinearInterval.mul,LinearInterval.Contains,LinearInterval.exact,
      LinearInterval.join,QAffine.productBounds,QAffine.curvature,QAffine.value] at hz
  · have he := List.mem_singleton.mp hi
    subst I
    norm_num [pos,LinearInterval.mul,LinearInterval.Contains,LinearInterval.exact,
      LinearInterval.join,QAffine.productBounds,QAffine.curvature,QAffine.value] at hz

/-- Reusing one witness is a stricter relation than independent choices. -/
theorem correlated_square_not_negative : ¬ ∃ x, Values 0 x ∧ (-1:ℝ) = x*x := by
  rintro ⟨x,_,h⟩
  nlinarith [sq_nonneg x]

theorem negative_still_enclosed : ∃ I ∈ signs.mul signs, I.Contains 0 (-1) :=
  products_sound.1 0 (-1) mixed_product_actual

theorem square_contract : signs.square.SoundOn everywhere (SquareValues Values) :=
  cover_square_domain_sound contract

theorem square_coefficients : signs.square.map (fun I => (I.lower,I.upper)) =
    [(⟨1,1⟩,⟨1,1⟩),(⟨1,1⟩,⟨1,1⟩)] := by decide +kernel

theorem square_exact (t z : ℝ) : SquareValues Values t z ↔
    t ∈ Set.Icc (0:ℝ) 1 ∧ z = 1 := by
  constructor
  · rintro ⟨x,⟨ht,hx⟩,rfl⟩
    refine ⟨ht,?_⟩
    rcases hx with rfl | rfl <;> norm_num
  · rintro ⟨ht,rfl⟩
    exact ⟨1,⟨ht,Or.inr rfl⟩,by norm_num⟩

/-- Preserve the choice until after the shared-witness operation. -/
theorem coalesce_after_square_succeeds : signs.square.coalesce.recip?.isSome := by
  decide +kernel

/-- Early coalescing loses the separation; failure remains unknown despite
actual squared values being exactly one throughout the parameter domain. -/
theorem coalesce_before_square_unknown : signs.coalesce.square.recip?.isNone := by
  decide +kernel

theorem unknown_despite_actual_square : signs.coalesce.square.recip?.isNone ∧
    SquareValues Values 0 1 :=
  ⟨coalesce_before_square_unknown,(square_exact 0 1).mpr ⟨by norm_num,rfl⟩⟩

/-- The smaller square cover cannot replace a general independent product. -/
theorem square_not_independent_product : ¬ signs.square.Covers (ProductValues Values Values) := by
  simpa [FiniteLinearCover.square,signs] using zipped_products_unsound

end Multivalued

end GeneralizedIntervalArithmetic.CoverPipelineChecks

#audit_namespace GeneralizedIntervalArithmetic.CoverPipelineChecks
