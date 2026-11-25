import GeneralFamilyDemotion
import GuardedPieceComposition
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Exact finite rational-expression graphs with retained partial-domain guards.
This is a proof-side representation, not a new expression language or backend. -/
namespace GeneralizedIntervalArithmetic.RationalFamilyClosure

abbrev Polynomial := MvPolynomial Bool ℚ

structure Code where
  numerator : Polynomial
  denominator : Polynomial
  guards : List Polynomial

/-- Every division keeps the divisor numerator as a nonzero constraint.
No cancellation removes inherited constraints. -/
noncomputable def compile : Expr → Code
  | .const q => ⟨MvPolynomial.C q,1,[]⟩
  | .x => ⟨MvPolynomial.X false,1,[]⟩
  | .y => ⟨MvPolynomial.X true,1,[]⟩
  | .add a b => let A := compile a; let B := compile b
    ⟨A.numerator*B.denominator+B.numerator*A.denominator,
      A.denominator*B.denominator,A.guards++B.guards⟩
  | .sub a b => let A := compile a; let B := compile b
    ⟨A.numerator*B.denominator-B.numerator*A.denominator,
      A.denominator*B.denominator,A.guards++B.guards⟩
  | .mul a b => let A := compile a; let B := compile b
    ⟨A.numerator*B.numerator,A.denominator*B.denominator,A.guards++B.guards⟩
  | .div a b => let A := compile a; let B := compile b
    ⟨A.numerator*B.denominator,A.denominator*B.numerator,
      A.guards++B.guards++[B.numerator]⟩

noncomputable def evalAt (x y : ℝ) : Polynomial →+* ℝ :=
  MvPolynomial.eval₂Hom (Rat.castHom ℝ) (fun b => if b then y else x)

def Admitted (c : Code) (x y : ℝ) : Prop := ∀g∈c.guards, evalAt x y g ≠ 0

noncomputable def result (c : Code) (x y : ℝ) : ℝ :=
  evalAt x y c.numerator / evalAt x y c.denominator

/-- Generated guards are sufficient for the generated denominator; they may
be strictly stronger because internal holes must survive algebraic cancellation. -/
theorem denominator_nonzero (e : Expr) (x y : ℝ) (h : Admitted (compile e) x y) :
    evalAt x y (compile e).denominator ≠ 0 := by
  induction e with
  | const q => simp [compile]
  | x => simp [compile]
  | y => simp [compile]
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    have hh : Admitted (compile a) x y ∧ Admitted (compile b) x y := by
      simpa [Admitted,compile,List.mem_append,or_imp,forall_and,and_assoc] using h
    simpa [compile] using mul_ne_zero (ha hh.1) (hb hh.2)
  | div a b ha hb =>
    have hh : (Admitted (compile a) x y ∧ Admitted (compile b) x y) ∧
        evalAt x y (compile b).numerator ≠ 0 := by
      simpa [Admitted,compile,List.mem_append,or_imp,forall_and,and_assoc] using h
    simpa [compile] using mul_ne_zero (ha hh.1.1) hh.2

/-- Exact graph of the existing strict partial semantics, evalAt one valuation. -/
theorem graph_exact (e : Expr) (x y z : ℝ) :
    Value x y e z ↔ Admitted (compile e) x y ∧ z = result (compile e) x y := by
  induction e generalizing z with
  | const q =>
    simp only [compile,Admitted,List.not_mem_nil,IsEmpty.forall_iff,implies_true,
      forall_const,true_and,result,map_one,div_one,evalAt,MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_C]
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact Value.const q
  | x =>
    simp only [compile,Admitted,List.not_mem_nil,IsEmpty.forall_iff,implies_true,
      forall_const,true_and,result,map_one,div_one,evalAt,MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_X,Bool.false_eq_true,if_false]
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact Value.x
  | y =>
    simp only [compile,Admitted,List.not_mem_nil,IsEmpty.forall_iff,implies_true,
      forall_const,true_and,result,map_one,div_one,evalAt,MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_X,if_true]
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact Value.y
  | add a b ha hb =>
    have hg : Admitted (compile (.add a b)) x y ↔
        Admitted (compile a) x y ∧ Admitted (compile b) x y := by
      simp [Admitted,compile,List.mem_append,or_imp,forall_and,and_assoc]
    have hv (hA : Admitted (compile a) x y) (hB : Admitted (compile b) x y) :
        result (compile (.add a b)) x y = result (compile a) x y + result (compile b) x y := by
      have h1 := denominator_nonzero a x y hA
      have h2 := denominator_nonzero b x y hB
      simp only [result,compile,map_add,map_mul]
      field_simp
    constructor
    · intro h; cases h with
      | add hA hB =>
        obtain ⟨hAA,rfl⟩ := (ha _).1 hA
        obtain ⟨hBB,rfl⟩ := (hb _).1 hB
        exact ⟨hg.2 ⟨hAA,hBB⟩,(hv hAA hBB).symm⟩
    · rintro ⟨h,rfl⟩
      have h := hg.1 h
      rw [hv h.1 h.2]
      exact Value.add ((ha _).2 ⟨h.1,rfl⟩) ((hb _).2 ⟨h.2,rfl⟩)
  | sub a b ha hb =>
    have hg : Admitted (compile (.sub a b)) x y ↔
        Admitted (compile a) x y ∧ Admitted (compile b) x y := by
      simp [Admitted,compile,List.mem_append,or_imp,forall_and,and_assoc]
    have hv (hA : Admitted (compile a) x y) (hB : Admitted (compile b) x y) :
        result (compile (.sub a b)) x y = result (compile a) x y - result (compile b) x y := by
      have h1 := denominator_nonzero a x y hA
      have h2 := denominator_nonzero b x y hB
      simp only [result,compile,map_sub,map_mul]
      field_simp
      ring
    constructor
    · intro h; cases h with
      | sub hA hB =>
        obtain ⟨hAA,rfl⟩ := (ha _).1 hA
        obtain ⟨hBB,rfl⟩ := (hb _).1 hB
        exact ⟨hg.2 ⟨hAA,hBB⟩,(hv hAA hBB).symm⟩
    · rintro ⟨h,rfl⟩
      have h := hg.1 h
      rw [hv h.1 h.2]
      exact Value.sub ((ha _).2 ⟨h.1,rfl⟩) ((hb _).2 ⟨h.2,rfl⟩)
  | mul a b ha hb =>
    have hg : Admitted (compile (.mul a b)) x y ↔
        Admitted (compile a) x y ∧ Admitted (compile b) x y := by
      simp [Admitted,compile,List.mem_append,or_imp,forall_and,and_assoc]
    have hv : result (compile (.mul a b)) x y = result (compile a) x y * result (compile b) x y := by
      simp [result,compile,div_mul_div_comm]
    constructor
    · intro h; cases h with
      | mul hA hB =>
        obtain ⟨hAA,rfl⟩ := (ha _).1 hA
        obtain ⟨hBB,rfl⟩ := (hb _).1 hB
        exact ⟨hg.2 ⟨hAA,hBB⟩,hv.symm⟩
    · rintro ⟨h,rfl⟩
      have h := hg.1 h
      rw [hv]
      exact Value.mul ((ha _).2 ⟨h.1,rfl⟩) ((hb _).2 ⟨h.2,rfl⟩)
  | div a b ha hb =>
    have hg : Admitted (compile (.div a b)) x y ↔
        (Admitted (compile a) x y ∧ Admitted (compile b) x y) ∧
          evalAt x y (compile b).numerator ≠ 0 := by
      simp [Admitted,compile,List.mem_append,or_imp,forall_and,and_assoc]
    have hv : result (compile (.div a b)) x y = result (compile a) x y / result (compile b) x y := by
      simp [result,compile,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
    constructor
    · intro h; cases h with
      | div hA hB hn =>
        obtain ⟨hAA,rfl⟩ := (ha _).1 hA
        obtain ⟨hBB,rfl⟩ := (hb _).1 hB
        have hn' : evalAt x y (compile b).numerator ≠ 0 := (div_ne_zero_iff.mp hn).1
        exact ⟨hg.2 ⟨⟨hAA,hBB⟩,hn'⟩,hv.symm⟩
    · rintro ⟨h,rfl⟩
      have h := hg.1 h
      rw [hv]
      exact Value.div ((ha _).2 ⟨h.1.1,rfl⟩) ((hb _).2 ⟨h.1.2,rfl⟩)
        (div_ne_zero h.2 (denominator_nonzero b x y h.1.2))

theorem domain_exact (e : Expr) (x y : ℝ) :
    (∃z, Value x y e z) ↔ Admitted (compile e) x y := by
  simp only [graph_exact,exists_eq_right]

/-- Polynomial graph equation; only the explicit guards license clearing the
compiled denominator. This introduces no value at an absent input. -/
theorem polynomial_graph_exact (e : Expr) (x y z : ℝ) :
    Value x y e z ↔ Admitted (compile e) x y ∧
      z * evalAt x y (compile e).denominator = evalAt x y (compile e).numerator := by
  rw [graph_exact]
  apply and_congr_right
  intro h
  exact eq_div_iff (denominator_nonzero e x y h)

/-- The extra constraint of a partial operation is constructed, not supplied
as a theorem premise. All inherited constraints remain present. -/
theorem division_domain (a b : Expr) (x y : ℝ) :
    Admitted (compile (.div a b)) x y ↔
      Admitted (compile a) x y ∧ Admitted (compile b) x y ∧
        result (compile b) x y ≠ 0 := by
  simp only [Admitted,compile,List.mem_append,List.mem_singleton,or_imp,forall_and,
    forall_eq,and_assoc]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro hb
  have hd := denominator_nonzero b x y hb
  simp [result,div_ne_zero_iff,hd]

/-- One original choice determines both coordinates and every AST occurrence. -/
def relation {α W : Type*} (e : Expr) (X Y : α → W → ℝ) (p : α) (w : W) (z : ℝ) : Prop :=
  Admitted (compile e) (X p w) (Y p w) ∧ z = result (compile e) (X p w) (Y p w)

theorem relation_exact {α W : Type*} (e : Expr) (X Y : α → W → ℝ)
    (p : α) (w : W) (z : ℝ) :
    relation e X Y p w z ↔ Value (X p w) (Y p w) e z := (graph_exact _ _ _ _).symm

/-- Exact represented image for arbitrary correlated inputs and external holes.
This also covers arbitrary unions of input pieces through the admission predicate. -/
theorem outputs_exact {α W : Type*} (e : Expr) (A : α → W → Prop) (X Y : α → W → ℝ) :
    GeneralFamilyDemotion.outputs A (relation e X Y) =
      GeneralFamilyDemotion.outputs A (fun p w z => Value (X p w) (Y p w) e z) := by
  funext p
  ext z
  simp only [GeneralFamilyDemotion.outputs,Set.mem_setOf_eq,relation_exact]

/-- Definite and possible classifications both retain the SAME admitted choices;
image equality alone would not suffice for this statement. -/
theorem classifications_exact {α W : Type*} (e : Expr) (A : α → W → Prop) (X Y : α → W → ℝ) :
    exactInputDomain A (relation e X Y) =
      exactInputDomain A (fun p w z => Value (X p w) (Y p w) e z) := by
  have he : relation e X Y = (fun p w z => Value (X p w) (Y p w) e z) := by
    funext p w z
    exact propext (relation_exact e X Y p w z)
  rw [he]

/-- Reuse the established hull/demotion theorem; a hull is an enclosure, not an
exact image, and its infinite bounds never become literal infinite values. -/
theorem family_hull_sound {α W : Type*} (e : Expr) (A : α → W → Prop) (X Y : α → W → ℝ) :
    GeneralFamilyDemotion.Sound
      (fun p => ExtendedImageHull.hull (GeneralFamilyDemotion.outputs A (relation e X Y) p))
      (exactInputDomain A (relation e X Y)) A
      (fun p w z => Value (X p w) (Y p w) e z) := by
  rw [outputs_exact,classifications_exact]
  exact GeneralFamilyDemotion.exact_hull_sound _ _

/-- Existing finite open/closed guards remain untouched. The generated graph is
polynomial, not claimed expressible by the old affine half-space grammar. -/
theorem pieces_exact (cs ds : List FiniteGuardPieces.Piece) (e : Expr) (t z : ℝ) :
    (∃x y, x ∈ FiniteGuardPieces.pieces cs t ∧ y ∈ FiniteGuardPieces.pieces ds t ∧
      Admitted (compile e) x y ∧ z * evalAt x y (compile e).denominator =
        evalAt x y (compile e).numerator) ↔
    ∃x y, x ∈ FiniteGuardPieces.pieces cs t ∧ y ∈ FiniteGuardPieces.pieces ds t ∧ Value x y e z := by
  simp only [polynomial_graph_exact,and_assoc]

end GeneralizedIntervalArithmetic.RationalFamilyClosure
