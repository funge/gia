import QuadraticFamilies

/-! Finite rational specialization of §§2.9.3–5: exact promotion and a concrete
quadratic-to-affine demotion, retaining the same parameter and domain witnesses. -/
namespace GeneralizedIntervalArithmetic.FiniteFamilyChain
open QuadraticFamilies

/-- Exact promotion through the already proved endpoint and polynomial bases. -/
noncomputable def promote (I : LinearInterval) : Bounds 1 :=
  fromAffine (MultiAffineFamilies.fromLinear I)

theorem promote_contains (I : LinearInterval) (t : Fin 1 → ℝ) (z : ℝ) :
    (promote I).Contains t z ↔ I.Contains (t 0) z := by
  rw [promote,fromAffine_contains,MultiAffineFamilies.fromLinear_contains]

theorem constant_chain (I : QInterval) (t : Fin 1 → ℝ) (z : ℝ) :
    (promote (LinearInterval.constant I)).Contains t z ↔ I.Contains z := by
  rw [promote_contains,linear_constant_contains]

/-- For p+qt+rt², add the exact affine p+qt to the existing certified product
of t and rt. This supplies coefficients, rather than assuming bounding functions. -/
noncomputable def formBounds (a : Form 1) : LinearInterval :=
  (LinearInterval.exact ⟨a.affine.offset,a.affine.offset+a.affine.coeff 0⟩).add
    (QAffine.productBounds ⟨0,1⟩ ⟨0,a.cross 0 0⟩)

theorem formBounds_encloses (a : Form 1) {t : Fin 1 → ℝ}
    (ht : MultiAffineFamilies.Cube t) : (formBounds a).Contains (t 0) (a.value t) := by
  have h := linear_add_encloses
    ((linear_exact_contains ⟨a.affine.offset,a.affine.offset+a.affine.coeff 0⟩
      (t 0) _).mpr rfl)
    (affine_product_encloses (a:=⟨0,1⟩) (b:=⟨0,a.cross 0 0⟩) (ht 0))
  convert h using 1
  simp [Form.value,MultiAffineFamilies.Form.value,QAffine.value]
  ring

noncomputable def demote (I : Bounds 1) : LinearInterval :=
  ⟨(formBounds I.lower).lower,(formBounds I.upper).upper,by
    have ht : MultiAffineFamilies.Cube (fun _ : Fin 1=> (0:ℝ)) := fun _=>by norm_num
    have h := (formBounds_encloses I.lower ht).1.trans
      ((I.ordered _ ht).trans (formBounds_encloses I.upper ht).2)
    simpa [QAffine.value] using h,by
    have ht : MultiAffineFamilies.Cube (fun _ : Fin 1=> (1:ℝ)) := fun _=>by norm_num
    have h := (formBounds_encloses I.lower ht).1.trans
      ((I.ordered _ ht).trans (formBounds_encloses I.upper ht).2)
    simpa [QAffine.value] using h⟩

theorem demote_encloses (I : Bounds 1) {t z} (ht : MultiAffineFamilies.Cube t)
    (hz : I.Contains t z) : (demote I).Contains (t 0) z :=
  ⟨(formBounds_encloses I.lower ht).1.trans hz.1,
    hz.2.trans (formBounds_encloses I.upper ht).2⟩

theorem chain_encloses (I : Bounds 1) {t z} (ht : MultiAffineFamilies.Cube t)
    (hz : I.Contains t z) : (demote I).hull.Contains z :=
  linear_hull_encloses (ht 0) (demote_encloses I ht hz)

/-- Promotion and this demotion are exactly inverse on the affine subfamily. -/
theorem round_trip (I : LinearInterval) : demote (promote I) = I := by
  cases I
  simp [demote,promote,fromAffine,embed,MultiAffineFamilies.fromLinear,
    MultiAffineFamilies.fromQAffine,formBounds,LinearInterval.exact,LinearInterval.add,
    QAffine.add,QAffine.productBounds,QAffine.curvature]

theorem promote_injective : Function.Injective promote := by
  intro I J h
  simpa only [round_trip] using congrArg demote h

theorem affine_round_trip (I : LinearInterval) (t z : ℝ) :
    (demote (promote I)).Contains t z ↔ I.Contains t z := by rw [round_trip]

theorem constant_hull_round_trip (I : QInterval) :
    (demote (promote (LinearInterval.constant I))).hull = I := by
  rw [round_trip]
  cases I
  simp [LinearInterval.constant,LinearInterval.hull]

theorem constant_promote_injective :
    Function.Injective (fun I:QInterval => promote (LinearInterval.constant I)) := by
  intro I J h
  simpa only [constant_hull_round_trip] using
    congrArg (fun K : Bounds 1 => (demote K).hull) h

/-- Actual relation with a per-witness partial domain, not a declaration that
all values in a hull occur. Cube membership is part of actual definedness. -/
noncomputable def relation {W : Type*} (I : Bounds 1)
    (P : (Fin 1 → ℝ) → W → Prop) (t : Fin 1 → ℝ) (w : W) (z : ℝ) : Prop :=
  MultiAffineFamilies.Cube t ∧ P t w ∧ I.Contains t z

/-- The numeric inclusion is discharged by the concrete converter. Domain flags
remain the exact flags of the original same-witness relation, including holes. -/
theorem partial_chain {W : Type*} (I : Bounds 1)
    (A P : (Fin 1 → ℝ) → W → Prop) :
    GeneralFamilyDemotion.Sound (fun t=>{z|(demote I).Contains (t 0) z})
      (exactInputDomain A (relation I P)) A (relation I P) ∧
    GeneralFamilyDemotion.Sound (fun _=>{z|(demote I).hull.Contains z})
      (exactInputDomain A (relation I P)) A (relation I P) := by
  have hs := GeneralFamilyDemotion.exact_sound A (relation I P)
  constructor
  · intro t w ha
    exact ⟨fun z hz => demote_encloses I hz.1 hz.2.2,(hs t w ha).2⟩
  · intro t w ha
    exact ⟨fun z hz => chain_encloses I hz.1 hz.2.2,(hs t w ha).2⟩

/-- A coefficient-level inclusion certificate for any two demoted results;
all parameter quantification is discharged by the existing affine order theorem. -/
theorem demoted_inclusion_iff (I J : Bounds 1) :
    (∀t∈Set.Icc (0:ℝ) 1, ∀z, (demote I).Contains t z → (demote J).Contains t z) ↔
    (demote J).lower.atZero ≤ (demote I).lower.atZero ∧
    (demote J).lower.atOne ≤ (demote I).lower.atOne ∧
    (demote I).upper.atZero ≤ (demote J).upper.atZero ∧
    (demote I).upper.atOne ≤ (demote J).upper.atOne := by
  have h := FamilyDemotion.linear_inclusion_iff (demote I) (demote J)
  tauto

end GeneralizedIntervalArithmetic.FiniteFamilyChain
