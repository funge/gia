import MonotoneUnions
import AuditPolicy
namespace GeneralizedIntervalArithmetic.MonotoneUnionsChecks
open MonotoneUnions

theorem crossing_square : (fun x : ℝ => x^2) '' Set.Icc (-2) 2 = Set.Icc 0 4 := by
  convert square_crossing (l:= -2) (u:=2) (by norm_num) (by norm_num) using 1; norm_num

theorem genuinely_noninjective : Value (-1) 0 (.mul .x .x) 1 ∧
    Value 1 0 (.mul .x .x) 1 ∧ (-1:ℝ)≠1 := by
  norm_num [square_expression]

theorem decreasing_flags : (fun x : ℝ => x^2) '' window (-2) (-1) true false =
    window 1 4 false true := by
  convert decreasing_image (f:=fun x : ℝ => x^2) (l:= -2) (u:= -1)
    (by norm_num) (by fun_prop) (square_decreasing (by norm_num)) true false using 1; norm_num

def disjointOutputs : List FiniteGuardPieces.Piece :=
  squarePieces (-3) (-2) false false ++ squarePieces 0 1 false false

theorem disjoint_output_exact (t : ℝ) : FiniteGuardPieces.pieces disjointOutputs t =
    window 4 9 false false ∪ window 0 1 false false := by
  norm_num [disjointOutputs,FiniteGuardPieces.pieces_append,squarePieces,encode_exact]

theorem union_not_hull : (2:ℝ) ∉ FiniteGuardPieces.pieces disjointOutputs 0 ∧
    (4:ℝ) ∈ FiniteGuardPieces.pieces disjointOutputs 0 ∧
    (9:ℝ) ∈ FiniteGuardPieces.pieces disjointOutputs 0 := by
  norm_num [disjoint_output_exact,window]

theorem reversed_empty (t : ℝ) : FiniteGuardPieces.pieces (squarePieces 3 1 false false) t = ∅ := by
  simp [squarePieces,FiniteGuardPieces.pieces,IntervalSetDenotation.denote]

theorem singleton_controls (t : ℝ) :
    (4:ℝ) ∈ FiniteGuardPieces.pieces (squarePieces 2 2 false false) t ∧
    FiniteGuardPieces.pieces (squarePieces 2 2 true false) t = ∅ := by
  constructor
  · norm_num [squarePieces,encode_exact,window]
  · ext z
    norm_num [squarePieces,encode_exact,window]

def beforeOne : FiniteGuardPieces.Guard := [(⟨-1,0⟩,true)]
theorem external_guard_retained :
    (1:ℝ) ∉ FiniteGuardPieces.pieces (guardedSquares beforeOne 0 1 false false) 1 ∧
    Value 1 1 (.mul .x .x) 1 := by
  constructor
  · rw [guarded_square_exact beforeOne 0 1 false false 1 0 1]
    simp [beforeOne,FiniteGuardPieces.guardHolds,QAffine.value]
  · norm_num [square_expression]

/-- Copying open flags under weak monotonicity would incorrectly lose a constant image. -/
theorem weak_monotonicity_not_enough :
    Monotone (fun (_ : ℝ) => (0:ℝ)) ∧
    (0:ℝ) ∈ (fun (_ : ℝ) => (0:ℝ)) '' window 0 1 true true ∧
    (0:ℝ) ∉ window 0 0 true true := by
  exact ⟨fun _ _ _ => le_rfl,⟨1/2,by norm_num [window],rfl⟩,by norm_num [window]⟩

noncomputable def jump (x : ℝ) : ℝ := if x<0 then x else x+1

theorem jump_strict : StrictMono jump := by
  intro x y hxy
  unfold jump
  split_ifs <;> linarith

theorem continuity_needed : (1/2:ℝ) ∈ window (jump (-1)) (jump 1) false false ∧
    (1/2:ℝ) ∉ jump '' window (-1) 1 false false := by
  constructor
  · norm_num [window,jump]
  · rintro ⟨x,_,hx⟩
    unfold jump at hx
    split_ifs at hx <;> linarith

/-- Open at a pole is not enough to justify finite endpoint substitution:
Lean's totalized 1/0 cannot supply the missing endpoint limit. -/
theorem pole_endpoint_counterexample :
    (-2:ℝ) ∈ (fun x : ℝ => 1/x) '' window (-1) 0 false true ∧
    (-2:ℝ) ∉ window (1/(-1)) (1/0) false false := by
  exact ⟨⟨-1/2,by norm_num [window],by norm_num⟩,by norm_num [window]⟩

def reciprocal : Expr := .div (.const 1) .x
def m : FractionalProjection.Coefficients := ⟨0,1,1,0⟩
def polePieces (i : Bool) : List FiniteGuardPieces.Piece :=
  if i then encode 0 1 true false else encode (-1) 0 false true

theorem reciprocal_certificate : FractionalProjection.Certified m reciprocal := by
  norm_num [FractionalProjection.Certified,FractionalProjection.Coefficients.Regular,
    m,reciprocal,RationalFamilyClosure.compile]

theorem pole_union_exact (t z : ℝ) :
    (∃x, (∃i : Bool, x∈FiniteGuardPieces.pieces (polePieces i) t) ∧ Value x t reciprocal z) ↔
      ∃i : Bool, FractionalProjection.Describes m (polePieces i) reciprocal t z := by
  simpa using finite_fractional_projection (Finset.univ : Finset Bool) (fun _ => True)
    polePieces reciprocal (fun _ => m) (fun _ _ _ => reciprocal_certificate) t z

theorem pole_zero_absent (t : ℝ) :
    ¬∃x, (∃i : Bool, x∈FiniteGuardPieces.pieces (polePieces i) t) ∧ Value x t reciprocal 0 := by
  rw [pole_union_exact]
  simp [FractionalProjection.Describes,m]

theorem reference_queries :
    FiniteGuardPieces.test (squarePieces (-2) (-1) true false) 0 1 = true ∧
    FiniteGuardPieces.test (squarePieces (-2) (-1) true false) 0 4 = false ∧
    FiniteGuardPieces.test disjointOutputs 0 2 = false := by
  simp only [FiniteGuardPieces.test_exact]
  constructor
  · norm_num [squarePieces,encode_exact,window]
  constructor
  · have hn : (4:ℝ) ∉ FiniteGuardPieces.pieces (squarePieces (-2) (-1) true false) 0 := by
      norm_num [squarePieces,encode_exact,window]
    have he := FiniteGuardPieces.test_exact (squarePieces (-2) (-1) true false) 0 4
    cases h : FiniteGuardPieces.test (squarePieces (-2) (-1) true false) 0 4 <;> simp_all
  · have he := FiniteGuardPieces.test_exact disjointOutputs 0 2
    have hn := union_not_hull.1
    cases h : FiniteGuardPieces.test disjointOutputs 0 2 <;> simp_all

#eval [FiniteGuardPieces.test (squarePieces (-2) (-1) true false) 0 1,
  FiniteGuardPieces.test (squarePieces (-2) (-1) true false) 0 4,
  FiniteGuardPieces.test disjointOutputs 0 2,
  FiniteGuardPieces.test (squarePieces (-2) 2 false false) 0 0]
end GeneralizedIntervalArithmetic.MonotoneUnionsChecks
#audit_namespace GeneralizedIntervalArithmetic.MonotoneUnionsChecks
