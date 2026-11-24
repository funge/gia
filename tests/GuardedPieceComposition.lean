import GuardedPieceComposition
import AuditPolicy
namespace GeneralizedIntervalArithmetic.GuardedPieceCompositionChecks
open GuardedPieceComposition MixedEndpoints FiniteGuardPieces

def rising : Band := ⟨1,1,1,1,false,false,[(⟨-1/2,1/2⟩,true)]⟩
def one : Band := ⟨1,0,1,0,false,false,[]⟩
def composed : Expr := .div (.const 1) (.add .x .y)

theorem evaluated : (evaluate? rising one composed).isSome = true := by
  decide +kernel

def result : Result := (evaluate? rising one composed).get evaluated

theorem result_eq : evaluate? rising one composed = some result := by
  exact (Option.some_get evaluated).symm

theorem interior_admitted : admitted? result (1/4) = true := by decide +kernel
theorem hole_excluded : admitted? result (1/2) = false := by decide +kernel
theorem outside_excluded : admitted? result (-1) = false := by decide +kernel

/-- Same t supplies both coordinates and every occurrence in the existing AST. -/
theorem actual_value {t : ℝ} (ht : 0 ≤ t) (hu : t < 1/2) :
    Values rising one composed t (1/(2+t)) := by
  refine ⟨⟨ht,by linarith⟩,1+t,1,?_,?_,?_⟩
  · simp [rising,Band.denote,Band.lowerValue,Band.upperValue,guardHolds,QAffine.value]
    linarith
  · simp [one,Band.denote,Band.lowerValue,Band.upperValue,guardHolds]
  · have h : 1+t+1 = 2+t := by ring
    have hv := Value.div (Value.const (x:=1+t) (y:=1) 1)
      (Value.add Value.x Value.y) (by linarith : 1+t+1 ≠ 0)
    simpa [composed,h] using hv

theorem enclosed_value {t : ℝ} (ht : 0 ≤ t) (hu : t < 1/2) :
    result.values.Contains t (1/(2+t)) := evaluate_encloses result_eq (actual_value ht hu)

theorem absent_at_boundary : ¬ ∃ z, Values rising one composed (1/2) z := by
  intro h
  have := (admitted_exact result_eq (1/2)).2 (by simpa using h)
  rw [hole_excluded] at this
  contradiction

/-- Arithmetic on the unguarded closed numeric bands still has a value there. -/
theorem ignoring_guard_creates_value : Value (3/2) 1 composed (2/5) := by
  have h := Value.div (Value.const (x:=(3/2:ℝ)) (y:=1) 1)
    (Value.add Value.x Value.y) (by norm_num : (3/2:ℝ)+1 ≠ 0)
  norm_num [composed] at h ⊢
  exact h

/-- A failed whole-hull guard is unknown, even at a point with an actual value. -/
def pole : Band := ⟨0,1,0,1,false,false,[]⟩
def reciprocal : Expr := .div (.const 1) .x

theorem guard_failure : evaluate? pole one reciprocal = none := by
  have h : (evaluate? pole one reciprocal).isNone = true := by decide +kernel
  cases he : evaluate? pole one reciprocal <;> simp_all

theorem failed_but_defined : Values pole one reciprocal 1 1 := by
  refine ⟨by norm_num,1,1,?_,?_,?_⟩
  · norm_num [pole,Band.denote,Band.lowerValue,Band.upperValue,guardHolds]
  · norm_num [one,Band.denote,Band.lowerValue,Band.upperValue,guardHolds]
  · have h := Value.div (Value.const (x:=(1:ℝ)) (y:=1) 1) Value.x (by norm_num : (1:ℝ) ≠ 0)
    simpa [reciprocal] using h

theorem returned_hull : result.values.hull.lo = 1/3 ∧ result.values.hull.hi = 1/2 := by
  decide +kernel

def leftBand : Band := { one with guards := [(⟨-1/2,1/2⟩,true)] }
def rightBand : Band := { one with guards := [(⟨1/2,-1/2⟩,true)] }
def first (w : Bool) : Band := if w then rightBand else leftBand
def second (w : Bool) : Band := if w then leftBand else rightBand
def sumExpr : Expr := .add .x .y

def jointResult (w : Bool) : Result :=
  (evaluate? (first w) (second w) sumExpr).get (by cases w <;> decide +kernel)

theorem joint_result_eq (w : Bool) :
    evaluate? (first w) (second w) sumExpr = some (jointResult w) :=
  (Option.some_get _).symm

theorem joint_classification (t : ℝ) :
    (familyDomain [false,true] first second sumExpr).definite t =
      (resultDomain [false,true] jointResult).definite t ∧
    (familyDomain [false,true] first second sumExpr).possible t =
      (resultDomain [false,true] jointResult).possible t :=
  family_classification_exact _ _ _ _ _ (fun w _ => joint_result_eq w) t

theorem no_shared_choice (w : Bool) (t : ℝ) :
    ¬ ∃ z, Values (first w) (second w) sumExpr t z := by
  rintro ⟨z,_,x,y,hx,hy,_⟩
  cases w <;>
    simp [first,second,leftBand,rightBand,one,Band.denote,guardHolds,QAffine.value] at hx hy <;>
    linarith [hx.1,hy.1]

theorem separate_witnesses_do_not_prove_existence :
    (∃ w : Bool, (1:ℝ) ∈ (first w).denote (1/4)) ∧
    (∃ w : Bool, (1:ℝ) ∈ (second w).denote (1/4)) ∧
    Value (1:ℝ) 1 sumExpr 2 ∧
    ¬ ∃ w z, Values (first w) (second w) sumExpr (1/4) z := by
  refine ⟨⟨false,?_⟩,⟨true,?_⟩,?_,?_⟩
  · norm_num [first,leftBand,one,Band.denote,guardHolds,QAffine.value,Band.lowerValue,Band.upperValue]
  · norm_num [second,leftBand,one,Band.denote,guardHolds,QAffine.value,Band.lowerValue,Band.upperValue]
  · convert (Value.add (Value.x (x:=(1:ℝ)) (y:=1)) Value.y) using 1; norm_num [sumExpr]
  · rintro ⟨w,z,h⟩
    exact no_shared_choice w (1/4) ⟨z,h⟩

theorem both_generated_guards_reject : admitted? (jointResult false) (1/4) = false ∧
    admitted? (jointResult true) (1/4) = false := by decide +kernel

def executableControls : IO Unit := do
  let got := [admitted? result (1/4), admitted? result (1/2), admitted? result (-1),
    (evaluate? pole one reciprocal).isNone, admitted? (jointResult false) (1/4),
    admitted? (jointResult true) (1/4)]
  unless got == [true,false,false,true,false,false] do
    throw (IO.userError "guarded piece composition reference regression")
#eval executableControls

#audit_namespace GeneralizedIntervalArithmetic.GuardedPieceCompositionChecks
end GeneralizedIntervalArithmetic.GuardedPieceCompositionChecks
