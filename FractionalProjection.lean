import RationalFamilyClosure
import PointDomains

/-! Exact witness elimination for certified fractional-linear value maps.
The inherited expression domain remains separate from its simplified value. -/
namespace GeneralizedIntervalArithmetic.FractionalProjection
open RationalFamilyClosure

structure Coefficients where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving DecidableEq, Repr

def Coefficients.Regular (m : Coefficients) : Prop := m.a*m.d-m.b*m.c ≠ 0

/-- Algebraic identities, not an assumed semantic value/domain theorem.
Internal guards of `e` are retained even when its final polynomials simplify. -/
def Certified (m : Coefficients) (e : Expr) : Prop :=
  m.Regular ∧
  (compile e).numerator * (MvPolynomial.C m.c * MvPolynomial.X false + MvPolynomial.C m.d) =
    (MvPolynomial.C m.a * MvPolynomial.X false + MvPolynomial.C m.b) * (compile e).denominator

theorem certified_identity {m : Coefficients} {e : Expr} (h : Certified m e) (x t : ℝ) :
    evalAt x t (compile e).numerator * ((m.c:ℝ)*x+m.d) =
      ((m.a:ℝ)*x+m.b) * evalAt x t (compile e).denominator := by
  have he := congrArg (evalAt x t) h.2
  simpa [evalAt,MvPolynomial.coe_eval₂Hom] using he

noncomputable def inverse (m : Coefficients) (z : ℝ) : ℝ :=
  ((m.d:ℝ)*z-m.b)/((m.a:ℝ)-m.c*z)

def inverseQ (m : Coefficients) (z : ℚ) : ℚ := (m.d*z-m.b)/(m.a-m.c*z)

theorem inverse_cast (m : Coefficients) (z : ℚ) :
    (inverseQ m z : ℝ) = inverse m (z:ℝ) := by simp [inverseQ,inverse]

theorem regular_real {m : Coefficients} (h : m.Regular) :
    (m.a:ℝ)*m.d-m.b*m.c ≠ 0 := by exact_mod_cast h

/-- A finite output at the missing inverse denominator cannot arise under a
nonzero determinant; this excludes an asymptotic value, not an infinity tag. -/
theorem inverse_unique {m : Coefficients} (h : m.Regular) {x z : ℝ}
    (he : z*((m.c:ℝ)*x+m.d) = (m.a:ℝ)*x+m.b) :
    (m.a:ℝ)-m.c*z ≠ 0 ∧ x = inverse m z := by
  have hd := regular_real h
  have hn : (m.a:ℝ)-m.c*z ≠ 0 := by
    intro hh
    have hb : (m.d:ℝ)*z=m.b := by
      nlinarith [congrArg (fun v : ℝ => v*x) hh]
    apply hd
    nlinarith [congrArg (fun v : ℝ => v*m.d) hh, congrArg (fun v : ℝ => v*m.c) hb]
  refine ⟨hn,?_⟩
  apply (eq_div_iff hn).2
  nlinarith

theorem inverse_equation (m : Coefficients) {z : ℝ}
    (h : (m.a:ℝ)-m.c*z ≠ 0) :
    z*((m.c:ℝ)*inverse m z+m.d) = (m.a:ℝ)*inverse m z+m.b := by
  have he := (div_mul_cancel₀ ((m.d:ℝ)*z-m.b) h)
  change inverse m z * ((m.a:ℝ)-m.c*z) = (m.d:ℝ)*z-m.b at he
  nlinarith

theorem inverse_denominator_nonzero {m : Coefficients} (h : m.Regular) {z : ℝ}
    (hn : (m.a:ℝ)-m.c*z ≠ 0) : (m.c:ℝ)*inverse m z+m.d ≠ 0 := by
  have he : (m.c:ℝ)*inverse m z+m.d =
      ((m.a:ℝ)*m.d-m.b*m.c)/((m.a:ℝ)-m.c*z) := by
    unfold inverse
    field_simp
    ring
  rw [he]
  exact div_ne_zero (regular_real h) hn

/-- Every actual value determines its unique original input. -/
theorem value_input {m : Coefficients} {e : Expr} (h : Certified m e)
    {x t z : ℝ} (hv : Value x t e z) :
    (m.a:ℝ)-m.c*z ≠ 0 ∧ x = inverse m z := by
  have he := (polynomial_graph_exact e x t z).1 hv
  have he' : z*((m.c:ℝ)*x+m.d) = (m.a:ℝ)*x+m.b := by
    apply mul_right_cancel₀ (denominator_nonzero e x t he.1)
    calc
      (z*((m.c:ℝ)*x+m.d))*evalAt x t (compile e).denominator =
          (z*evalAt x t (compile e).denominator)*((m.c:ℝ)*x+m.d) := by ring
      _ = evalAt x t (compile e).numerator*((m.c:ℝ)*x+m.d) := by rw [he.2]
      _ = _ := certified_identity h x t
  exact inverse_unique h.1 he'

/-- Original pieces, parameter and expression guards are all tested at the same
uniquely reconstructed input. No existential input remains in this descriptor. -/
def Describes (m : Coefficients) (cs : List FiniteGuardPieces.Piece)
    (e : Expr) (t z : ℝ) : Prop :=
  (m.a:ℝ)-m.c*z ≠ 0 ∧ inverse m z ∈ FiniteGuardPieces.pieces cs t ∧
    Admitted (compile e) (inverse m z) t

def Image (cs : List FiniteGuardPieces.Piece) (e : Expr) (t : ℝ) : Set ℝ :=
  {z | ∃x, x ∈ FiniteGuardPieces.pieces cs t ∧ Value x t e z}

theorem projection_exact {m : Coefficients} {e : Expr} (h : Certified m e)
    (cs : List FiniteGuardPieces.Piece) (t z : ℝ) :
    z ∈ Image cs e t ↔ Describes m cs e t z := by
  constructor
  · rintro ⟨x,hx,hv⟩
    obtain ⟨hn,rfl⟩ := value_input h hv
    exact ⟨hn,hx,((graph_exact e _ _ _).1 hv).1⟩
  · rintro ⟨hn,hx,hg⟩
    refine ⟨inverse m z,hx,(polynomial_graph_exact e _ _ _).2 ⟨hg,?_⟩⟩
    apply mul_right_cancel₀ (inverse_denominator_nonzero h.1 hn)
    calc
      (z*evalAt (inverse m z) t (compile e).denominator)*((m.c:ℝ)*inverse m z+m.d) =
          (z*((m.c:ℝ)*inverse m z+m.d))*evalAt (inverse m z) t (compile e).denominator := by ring
      _ = ((m.a:ℝ)*inverse m z+m.b)*evalAt (inverse m z) t (compile e).denominator := by
        rw [inverse_equation m hn]
      _ = _ := (certified_identity h (inverse m z) t).symm

/-- Effective rational membership, reusing the existing exact singleton evaluator.
This does not execute the noncomputable polynomial compiler or a native backend. -/
def test (m : Coefficients) (cs : List FiniteGuardPieces.Piece) (e : Expr) (t z : ℚ) : Bool :=
  if m.a-m.c*z = 0 then false else
    FiniteGuardPieces.test cs t (inverseQ m z) &&
      (eval exactBackend (.point (inverseQ m z)) (.point t) e).isSome

theorem test_exact {m : Coefficients} {e : Expr} (h : Certified m e)
    (cs : List FiniteGuardPieces.Piece) (t z : ℚ) :
    test m cs e t z = true ↔ (z:ℝ) ∈ Image cs e (t:ℝ) := by
  rw [projection_exact h]
  unfold test
  by_cases hn : m.a-m.c*z = 0
  · have hn' : (m.a:ℝ)-m.c*(z:ℝ)=0 := by exact_mod_cast hn
    simp [hn,Describes,hn']
  · have hn' : (m.a:ℝ)-m.c*(z:ℝ)≠0 := by exact_mod_cast hn
    simp only [hn,if_false,Bool.and_eq_true,FiniteGuardPieces.test_exact,
      eval_point_defined_iff,domain_exact,inverse_cast,Describes,hn',true_and]
    exact ⟨fun hh => ⟨hn',hh⟩,And.right⟩

theorem test_false_iff {m : Coefficients} {e : Expr} (h : Certified m e)
    (cs : List FiniteGuardPieces.Piece) (t z : ℚ) :
    test m cs e t z = false ↔ (z:ℝ) ∉ Image cs e (t:ℝ) := by
  rw [←test_exact h]
  cases test m cs e t z <;> simp

/-- Restricting the input never manufactures an output; exact membership is
preserved even if the restriction contains open boundaries or interior holes. -/
theorem image_mono {cs ds : List FiniteGuardPieces.Piece} (e : Expr) (t : ℝ)
    (h : FiniteGuardPieces.pieces cs t ⊆ FiniteGuardPieces.pieces ds t) :
    Image cs e t ⊆ Image ds e t := by
  rintro z ⟨x,hx,hv⟩
  exact ⟨x,h hx,hv⟩

theorem image_union (cs ds : List FiniteGuardPieces.Piece) (e : Expr) (t : ℝ) :
    Image (cs++ds) e t = Image cs e t ∪ Image ds e t := by
  ext z
  simp only [Image,FiniteGuardPieces.pieces_append,Set.mem_setOf_eq,Set.mem_union]
  aesop

/-- Unlike general image maps, certified regular fractional-linear maps also
preserve intersections: the output forces the SAME input in both pieces. -/
theorem image_inter {m : Coefficients} {e : Expr} (h : Certified m e)
    (cs ds : List FiniteGuardPieces.Piece) (t : ℝ) :
    Image (FiniteGuardPieces.meet cs ds) e t = Image cs e t ∩ Image ds e t := by
  ext z
  simp only [projection_exact h,Describes,FiniteGuardPieces.meet_exact,Set.mem_inter_iff]
  tauto

/-- Existing closed-hull demotion remains an overapproximation of this exact
possibly open/disconnected/unbounded real image. -/
theorem hull_encloses (cs : List FiniteGuardPieces.Piece) (e : Expr) (t : ℝ) :
    Image cs e t ⊆ ExtendedImageHull.hull (Image cs e t) := ExtendedImageHull.sound _

end GeneralizedIntervalArithmetic.FractionalProjection
