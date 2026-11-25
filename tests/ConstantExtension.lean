import ConstantExtension
import HansenRealSets
import AuditPolicy
namespace GeneralizedIntervalArithmetic.ConstantExtensionChecks
open ConstantExtension GeneralFamilyDemotion

/-- Actual compatible demoters, not an assumed homomorphism equation. -/
theorem projected_nary {n : ℕ} (I : Fin n → EReal × EReal)
    (G : (Fin n → ℝ) → ℝ → Prop) :
    family (projectDown (P:=Unit)) projectUp (fun p x => ∀ i,
      x i ∈ ExtendedImageHull.interval ((constant (P:=Unit) (I i)).1 p)
        ((constant (P:=Unit) (I i)).2 p)) G =
    constant (P:=Unit) (scalar (fun x => ∀ i,
      x i ∈ ExtendedImageHull.interval (I i).1 (I i).2) G) :=
  interval_homomorphism projectDown_compatible projectUp_compatible I G

theorem empty_image : scalar (fun _ : Unit => True) (fun _ _ => False) = (⊤,⊥) := by
  simp [scalar,outputs,ExtendedImageHull.lower,ExtendedImageHull.upper]

theorem unbounded_image : scalar (fun _ : Unit => True) (fun _ _ => True) = (⊥,⊤) := by
  have hs : outputs (fun (_ : Unit) (_ : Unit) => True) (fun _ _ (_ : ℝ) => True) () = Set.univ := by
    ext z; simp [outputs]
  change (ExtendedImageHull.lower _,ExtendedImageHull.upper _) = _
  rw [hs]
  exact Prod.ext (ExtendedImageHull.lower_unbounded not_bddBelow_univ)
    (ExtendedImageHull.upper_unbounded not_bddAbove_univ)

/-- Cancellation does not remove the input guard from the operation graph. -/
theorem guarded_cancellation :
    scalar (fun x : ℝ => x∈Set.Icc (-1) 1)
      (fun x z => x≠0 ∧ z=x/x) = (1,1) := by
  have hs : outputs (fun (_ : Unit) (x : ℝ) => x∈Set.Icc (-1) 1)
      (fun _ x z => x≠0 ∧ z=x/x) () = {1} := by
    ext z
    constructor
    · rintro ⟨x,_,hx,rfl⟩; simp [hx]
    · intro h
      exact ⟨1,by norm_num,by norm_num,by simpa using h⟩
  change (ExtendedImageHull.lower _,ExtendedImageHull.upper _) = _
  rw [hs]
  simp [ExtendedImageHull.lower,ExtendedImageHull.upper]

theorem cancellation_hole : ¬∃ z : ℝ, (0:ℝ)≠0 ∧ z=0/0 := by simp

noncomputable def looseDown (f : Unit → EReal) : Unit → EReal := fun p => min (f p) (-1)
noncomputable def looseUp (f : Unit → EReal) : Unit → EReal := fun p => max (f p) 1

theorem loose_outward :
    (∀ f p, looseDown f p ≤ f p) ∧ (∀ f p, f p ≤ looseUp f p) :=
  ⟨fun _ _ => min_le_left _ _,fun _ _ => le_max_left _ _⟩

/-- Outward inclusion alone does not yield the printed operation equality. -/
theorem loose_not_homomorphic :
    family looseDown looseUp (fun _ (_ : Unit) => True) (fun _ z => z=0) ≠
      constant (P:=Unit) (scalar (fun _ : Unit => True) (fun _ z => z=0)) := by
  intro h
  have he := congrArg (fun b => b.1 ()) h
  norm_num [family,scalar,outputs,constant,looseDown,ExtendedImageHull.lower] at he
  have hf : ¬(0:EReal)≤-1 := by
    change ¬((0:ℝ):EReal) ≤ ((-1:ℝ):EReal)
    rw [EReal.coe_le_coe_iff]
    norm_num
  exact hf he

theorem loose_not_compatible : ¬LowerCompatible looseDown := by
  intro h
  have he := congrFun (lower_fixes_constants h 0) ()
  norm_num [looseDown] at he
  have hf : ¬(0:EReal)≤-1 := by
    change ¬((0:ℝ):EReal) ≤ ((-1:ℝ):EReal)
    rw [EReal.coe_le_coe_iff]
    norm_num
  exact hf he

/-- This reuses existing real coefficients; it does not generalize the separate
rational-coefficient MultiAffineFamilies API or invent infinite arithmetic. -/
theorem real_coefficients_existing {n : ℕ} (p : ℝ) (q : Fin n → ℝ) (t : Fin n → ℝ) :
    HansenRealSets.values {p} (fun i => {q i}) t =
      {HansenCoefficients.value (p,q) t} := by
  ext z
  simp only [HansenRealSets.values,HansenRealSets.admissible,
    Set.mem_setOf_eq,Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,hz⟩
    have he : b=q := funext hb
    change a=p at ha
    subst a; subst b; exact hz
  · intro h
    exact ⟨(p,q),⟨rfl,fun _ => rfl⟩,h⟩

/-- The source-supported pre-lambda carrier guard, using structural tags, not
an invented numerical not-equal predicate. -/
theorem scoped_positive_infinity (v : ExceptionalComparisons.Value)
    (hl : v≠.undefined) (hn : v≠.negInf) :
    ExceptionalComparisons.addObservation v .posInf = some .posInf := by
  cases v <;> simp_all [ExceptionalComparisons.addObservation]

theorem lambda_guard_not_covered :
    ExceptionalComparisons.Value.undefined ≠ .negInf ∧
    ExceptionalComparisons.addObservation .undefined .posInf = none := by
  constructor
  · intro h; cases h
  · rfl

end GeneralizedIntervalArithmetic.ConstantExtensionChecks
#audit_namespace GeneralizedIntervalArithmetic.ConstantExtensionChecks
