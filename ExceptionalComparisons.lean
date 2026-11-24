import ExtendedImageHull
import SquareRootDomains
import PartialRealArithmetic

/-! Explicit common subset of Tupper §§2.5.1–2. Source comparison observations
are not Lean equality, EReal bound order, or IEEE instructions. `none` means
unmodeled in this table, NOT lambda or a hardware failure. -/
namespace GeneralizedIntervalArithmetic.ExceptionalComparisons

/-- Real payloads idealize finite numeric meanings; this is not the IEEE carrier. -/
inductive Value where
  | finite (x : ℝ)
  | negInf
  | posInf
  | undefined

/-- The five numerical predicates named in §2.1. No numerical `ne` is inferred. -/
inductive Op where
  | lt | eq | le | ge | gt
  deriving DecidableEq

def finiteMeaning : Op → ℝ → ℝ → Prop
  | .lt, x, y => x < y
  | .eq, x, y => x = y
  | .le, x, y => x ≤ y
  | .ge, x, y => y ≤ x
  | .gt, x, y => y < x

noncomputable def observe : Op → Value → Value → Option Bool := by
  classical
  exact fun op a b => match a, b with
    | .undefined, _ => some false
    | _, .undefined => some false
    | .finite x, .finite y => some (decide (finiteMeaning op x y))
    | .negInf, .negInf => some false
    | .posInf, .posInf => some false
    | _, _ => none

/-- A representation map for comparison with existing mathematical bounds.
It is not claimed to be Tupper's full promotion or an arithmetic homomorphism. -/
noncomputable def bound : Value → Option EReal
  | .finite x => some x
  | .negInf => some ⊥
  | .posInf => some ⊤
  | .undefined => none

theorem finite_agreement (op : Op) (x y : ℝ) :
    observe op (.finite x) (.finite y) = some (by classical exact decide (finiteMeaning op x y)) := by
  rfl

theorem undefined_left (op : Op) (v : Value) :
    observe op .undefined v = some false := by cases v <;> rfl

theorem undefined_right (op : Op) (v : Value) :
    observe op v .undefined = some false := by cases v <;> rfl

theorem same_sign_infinities (op : Op) :
    observe op .negInf .negInf = some false ∧ observe op .posInf .posInf = some false := ⟨rfl,rfl⟩

/-- No chosen answer for the six mixed finite/infinite shapes. -/
theorem mixed_unmodeled (op : Op) (x : ℝ) :
    observe op .negInf (.finite x) = none ∧
    observe op (.finite x) .negInf = none ∧
    observe op .posInf (.finite x) = none ∧
    observe op (.finite x) .posInf = none ∧
    observe op .negInf .posInf = none ∧
    observe op .posInf .negInf = none := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem lt_true_iff (a b : Value) : observe .lt a b = some true ↔
    ∃ x y, a = .finite x ∧ b = .finite y ∧ x < y := by
  cases a <;> cases b <;> simp [observe,finiteMeaning]

theorem eq_true_iff (a b : Value) : observe .eq a b = some true ↔
    ∃ x, a = .finite x ∧ b = .finite x := by
  cases a <;> cases b <;> simp [observe,finiteMeaning,eq_comm]

/-- Observed strict comparison agrees with mathematical bound order only when
both bound interpretations exist and the table supplies an observation. -/
theorem strict_bound_agreement {a b : Value} {u v : EReal} {r : Bool}
    (ha : bound a = some u) (hb : bound b = some v)
    (h : observe .lt a b = some r) : r = (by classical exact decide (u < v)) := by
  classical
  cases a <;> cases b <;> simp_all [bound,observe,finiteMeaning]
  subst u
  subst v
  simpa using h.symm

/-- Finite equality agrees with bound equality. The exceptional analogue fails. -/
theorem finite_bound_equality (x y : ℝ) :
    observe .eq (.finite x) (.finite y) = some (by classical exact decide ((x:EReal) = (y:EReal))) := by
  simp [observe,finiteMeaning]

theorem exceptional_equality_is_not_bound_equality :
    observe .eq .posInf .posInf = some false ∧
    bound .posInf = some (⊤ : EReal) ∧ (⊤ : EReal) = ⊤ := ⟨rfl,rfl,rfl⟩

theorem source_equality_not_reflexive : ¬ ∀ v : Value, observe .eq v v = some true := by
  intro h
  have hh := h .posInf
  simp [observe] at hh

/-- False equality is not a proof of structural inequality. -/
theorem false_equality_not_structural_ne :
    ∃ v : Value, observe .eq v v = some false ∧ v = v := ⟨.posInf,rfl,rfl⟩

/-- A finite-only bridge to the existing real-member interval definition. -/
theorem finite_interval_membership (l u x : ℝ) :
    x ∈ ExtendedImageHull.interval (l:EReal) (u:EReal) ↔
      observe .lt (.finite x) (.finite l) = some false ∧
      observe .lt (.finite u) (.finite x) = some false := by
  simp [ExtendedImageHull.interval,observe,finiteMeaning,not_lt]

/-- Naively extending the finite membership test would admit lambda. -/
theorem undefined_passes_negated_tests (l u : ℝ) :
    observe .lt .undefined (.finite l) = some false ∧
    observe .lt (.finite u) .undefined = some false ∧ bound .undefined = none := ⟨rfl,rfl,rfl⟩

/-- Ideal real addition plus the explicitly displayed positive-infinity rule.
Other exceptional rows are unmodeled, not assumed undefined or IEEE-like. -/
noncomputable def addObservation : Value → Value → Option Value
  | .finite x, .finite y => some (.finite (x+y))
  | .finite _, .posInf => some .posInf
  | .posInf, .posInf => some .posInf
  | _, _ => none

/-- Partial real square root on finite payloads. Source λ is a modeled result;
`none` is reserved for unmodeled exceptional inputs. -/
noncomputable def sqrtObservation : Value → Option Value := by
  classical
  exact fun v => match v with
    | .finite x => if x < 0 then some .undefined else some (.finite (Real.sqrt x))
    | _ => none

theorem add_finite_agreement (x y z : ℝ) :
    addObservation (.finite x) (.finite y) = some (.finite z) ↔
      PartialRealArithmetic.addRel x y z := by
  simp [addObservation,eq_comm]

/-- The source equation is a result specification, not its numerical eq operator. -/
theorem add_positive_infinity_cases (x : ℝ) :
    addObservation (.finite x) .posInf = some .posInf ∧
    addObservation .posInf .posInf = some .posInf := ⟨rfl,rfl⟩

theorem add_missing_rows :
    addObservation .negInf .posInf = none ∧
    addObservation .undefined .posInf = none ∧
    addObservation .posInf (.finite 0) = none := ⟨rfl,rfl,rfl⟩

theorem sqrt_negative (x : ℝ) (hx : x < 0) :
    sqrtObservation (.finite x) = some .undefined := by
  simp [sqrtObservation,hx]

theorem sqrt_nonnegative (x : ℝ) (hx : 0 ≤ x) :
    sqrtObservation (.finite x) = some (.finite (Real.sqrt x)) := by
  simp [sqrtObservation,not_lt_of_ge hx]

/-- Exact agreement with the already existing partial real root relation. -/
theorem sqrt_finite_agreement (x z : ℝ) :
    sqrtObservation (.finite x) = some (.finite z) ↔
      SqrtValues (fun (_ : Unit) (_ : Unit) y => y = x) () () z := by
  classical
  simp only [SqrtValues]
  simp only [exists_eq_left]
  simp only [sqrtObservation]
  split_ifs with h
  · simp [not_le_of_gt h]
  · simp [le_of_not_gt h,eq_comm]

theorem sqrt_defined_iff (x : ℝ) :
    (∃ z, sqrtObservation (.finite x) = some (.finite z)) ↔ 0 ≤ x := by
  simp only [sqrt_finite_agreement,SqrtValues]
  simp

theorem sqrt_exceptional_unmodeled :
    sqrtObservation .negInf = none ∧ sqrtObservation .posInf = none ∧
    sqrtObservation .undefined = none := ⟨rfl,rfl,rfl⟩

/-- Bound arithmetic agreement only for the modeled addition rows, with
successful bound interpretations; no full source promotion theorem is claimed. -/
theorem add_bound_agreement {a b c : Value} {u v : EReal}
    (ha : bound a = some u) (hb : bound b = some v)
    (h : addObservation a b = some c) : bound c = some (u+v) := by
  cases a <;> cases b <;> simp only [bound] at ha hb
  all_goals cases ha
  all_goals cases hb
  all_goals simp only [addObservation] at h
  all_goals cases h
  all_goals simp [bound,EReal.coe_add]


/-- Undefined root is not the totalized real square-root value zero. -/
theorem negative_root_not_totalized (x : ℝ) (hx : x < 0) :
    Real.sqrt x = 0 ∧ sqrtObservation (.finite x) ≠ some (.finite 0) := by
  exact ⟨Real.sqrt_eq_zero_of_nonpos (le_of_lt hx),by simp [sqrt_negative x hx]⟩


/-- Derived non-strict comparison uses disjunction, never complement of `gt`.
Missing observations remain missing; this is not three-valued source logic. -/
def observedOr : Option Bool → Option Bool → Option Bool
  | some a, some b => some (a || b)
  | _, _ => none

/-- Converse definition of greater-than, including unmodeled rows. -/
theorem gt_converse (a b : Value) : observe .gt a b = observe .lt b a := by
  cases a <;> cases b <;> simp [observe, finiteMeaning]

/-- Standard non-strict predicate definition on the supported source rows. -/
theorem le_disjunction (a b : Value) :
    observe .le a b = observedOr (observe .lt a b) (observe .eq a b) := by
  cases a <;> cases b <;> simp [observe, finiteMeaning, observedOr, le_iff_lt_or_eq]

theorem ge_converse (a b : Value) : observe .ge a b = observe .le b a := by
  cases a <;> cases b <;> simp [observe, finiteMeaning]

theorem equality_symmetric (a b : Value) : observe .eq a b = observe .eq b a := by
  cases a <;> cases b <;> simp [observe, finiteMeaning, eq_comm]

theorem ge_disjunction (a b : Value) :
    observe .ge a b = observedOr (observe .gt a b) (observe .eq a b) := by
  rw [ge_converse, le_disjunction, gt_converse, equality_symmetric a b]

/-- New non-strict observations do not import EReal reflexivity at infinity. -/
theorem le_true_iff (a b : Value) : observe .le a b = some true ↔
    ∃ x y, a = .finite x ∧ b = .finite y ∧ x ≤ y := by
  cases a <;> cases b <;> simp [observe, finiteMeaning]

theorem ge_true_iff (a b : Value) : observe .ge a b = some true ↔
    ∃ x y, a = .finite x ∧ b = .finite y ∧ y ≤ x := by
  cases a <;> cases b <;> simp [observe, finiteMeaning]

theorem gt_true_iff (a b : Value) : observe .gt a b = some true ↔
    ∃ x y, a = .finite x ∧ b = .finite y ∧ y < x := by
  cases a <;> cases b <;> simp [observe, finiteMeaning]

/-- A comparison result is supplied exactly for these shapes, uniformly in
all five predicates. Missing observations are not a source unorderedness claim. -/
theorem observation_available (op : Op) (a b : Value) :
    (∃ r, observe op a b = some r) ↔
      a = .undefined ∨ b = .undefined ∨
      (∃ x y, a = .finite x ∧ b = .finite y) ∨
      (a = .negInf ∧ b = .negInf) ∨ (a = .posInf ∧ b = .posInf) := by
  cases a <;> cases b <;> simp [observe]

/-- Numerically false `gt` does not imply numerically true `le`. -/
theorem not_complement_at_infinity :
    observe .le .posInf .posInf = some false ∧
    (observe .gt .posInf .posInf).map Bool.not = some true := ⟨rfl, rfl⟩

/-- Finite payloads permit all five comparisons to use the bound map.
No corresponding non-strict theorem is claimed at infinity. -/
theorem finite_nonstrict_bound (x y : ℝ) :
    observe .le (.finite x) (.finite y) =
      some (by classical exact decide ((x : EReal) ≤ (y : EReal))) := by
  simp [observe, finiteMeaning]

end GeneralizedIntervalArithmetic.ExceptionalComparisons
