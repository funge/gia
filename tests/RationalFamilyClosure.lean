import RationalFamilyClosure
import AuditPolicy
namespace GeneralizedIntervalArithmetic.RationalFamilyClosureChecks
open RationalFamilyClosure

def inverseInverse : Expr := .div (.const 1) (.div (.const 1) .x)
def cancelled : Expr := .div (.sub (.mul .x .x) (.const 1)) (.sub .x (.const 1))

theorem inverse_inverse_guard (x y : ℝ) :
    Admitted (compile inverseInverse) x y ↔ x ≠ 0 := by
  simp [inverseInverse,compile,Admitted,evalAt,MvPolynomial.coe_eval₂Hom]

theorem inherited_hole : evalAt 0 0 (compile inverseInverse).denominator = 1 ∧
    ¬Admitted (compile inverseInverse) 0 0 ∧ ¬∃z, Value 0 0 inverseInverse z := by
  refine ⟨?_,by simp [inverse_inverse_guard],?_⟩
  · simp [inverseInverse,compile,evalAt,MvPolynomial.coe_eval₂Hom]
  · rw [domain_exact]; simp [inverse_inverse_guard]

theorem inverse_inverse_value (x y : ℝ) (hx : x ≠ 0) : Value x y inverseInverse x := by
  apply (graph_exact _ _ _ _).2
  refine ⟨(inverse_inverse_guard x y).2 hx,?_⟩
  simp [inverseInverse,result,compile,evalAt,MvPolynomial.coe_eval₂Hom]

theorem zero_does_not_erase_hole : ¬∃z,Value 0 0 (.mul (.const 0) (.div (.const 1) .x)) z := by
  rw [domain_exact]
  simp [compile,Admitted,evalAt,MvPolynomial.coe_eval₂Hom]

theorem cancelled_guard (x y : ℝ) : Admitted (compile cancelled) x y ↔ x ≠ 1 := by
  simp [cancelled,compile,Admitted,evalAt,MvPolynomial.coe_eval₂Hom,sub_ne_zero]

theorem cancelled_value (x y : ℝ) (hx : x ≠ 1) : Value x y cancelled (x+1) := by
  apply (polynomial_graph_exact _ _ _ _).2
  refine ⟨(cancelled_guard x y).2 hx,?_⟩
  simp [cancelled,compile,evalAt,MvPolynomial.coe_eval₂Hom]
  ring

theorem cancelled_missing_boundary (y : ℝ) : ¬∃z,Value 1 y cancelled z := by
  rw [domain_exact]; simp [cancelled_guard]

/-- Nonlinear two-variable hole: the actual product is tested, not its hull. -/
theorem nonlinear_domain (x y : ℝ) :
    Admitted (compile (.div (.const 1) (.sub (.mul .x .y) (.const 1)))) x y ↔ x*y ≠ 1 := by
  simp [compile,Admitted,evalAt,MvPolynomial.coe_eval₂Hom,sub_ne_zero]

/-- Same uncertain coefficient is used at both occurrences. -/
theorem shared_choice (w : ℝ) : relation (.sub .x .y)
    (fun (_ : Unit) w => w) (fun _ w => w) () w 0 := by
  rw [relation_exact]
  convert Value.sub (Value.x (x:=w) (y:=w)) (Value.y (x:=w) (y:=w)) using 1
  ring

theorem independent_rechoice : Value 0 1 (.sub .x .y) (-1) ∧
    ¬∃w : ℝ,Value w w (.sub .x .y) (-1) := by
  constructor
  · convert Value.sub (Value.x (x:=0) (y:=1)) (Value.y (x:=0) (y:=1)) using 1
    norm_num
  · rintro ⟨w,h⟩
    have hh := (graph_exact _ _ _ _).1 h
    simp [result,compile,evalAt,MvPolynomial.coe_eval₂Hom] at hh

/-- Preserve an open external boundary even when the arithmetic is defined. -/
theorem external_hole :
    GeneralFamilyDemotion.outputs (fun t (_ : Unit) => t < (1:ℝ))
      (relation (.add .x (.const 1)) (fun t _ => t) (fun _ _ => 0)) 1 = ∅ := by
  ext z
  simp [GeneralFamilyDemotion.outputs]

/-- No vacuous definite-domain classification for absent input choices. -/
theorem empty_classifications :
    ¬(exactInputDomain (fun (_ : Unit) (_ : ℝ) => False)
      (relation (.const 1) (fun _ w => w) (fun _ w => w))).definite () ∧
    ¬(exactInputDomain (fun (_ : Unit) (_ : ℝ) => False)
      (relation (.const 1) (fun _ w => w) (fun _ w => w))).possible () := by
  simp [exactInputDomain]

theorem partial_classifications :
    (exactInputDomain (fun (_ : Unit) (w : ℝ) => w=0 ∨ w=1)
      (relation inverseInverse (fun _ w => w) (fun _ _ => 0))).possible () ∧
    ¬(exactInputDomain (fun (_ : Unit) (w : ℝ) => w=0 ∨ w=1)
      (relation inverseInverse (fun _ w => w) (fun _ _ => 0))).definite () := by
  constructor
  · exact ⟨1,1,Or.inr rfl,(relation_exact _ _ _ _ _ _).2 (inverse_inverse_value 1 0 (by norm_num))⟩
  · intro h
    obtain ⟨z,hz⟩ := h.2 0 (Or.inl rfl)
    exact inherited_hole.2.2 ⟨z,(relation_exact _ _ _ _ _ _).1 hz⟩

/-- A single affine bound cannot be an exact representation of square even on
three points. Our polynomial graph is not secretly an affine-family closure. -/
theorem square_not_affine : ¬∃a : QAffine,
    a.value 0 = 0 ∧ a.value 1 = 1 ∧ a.value (1/2) = (1/4:ℝ) := by
  rintro ⟨a,h0,h1,hm⟩
  simp only [QAffine.value] at *
  norm_num at h0 h1 hm
  rw [h0,h1] at hm
  norm_num at hm

open FiniteGuardPieces in
def openUnitBand : List Piece :=
  (band [(⟨0,-1⟩,false),(⟨-1,0⟩,true)] ⟨0,1⟩ ⟨0,1⟩ false false).compile

open FiniteGuardPieces in
theorem open_band (t x : ℝ) : x ∈ pieces openUnitBand t ↔ 0 ≤ t ∧ t < 1 ∧ x=t := by
  rw [openUnitBand,band_exact]
  simp [guardHolds,QAffine.value,forall_and]
  constructor
  · rintro ⟨⟨h0,h1⟩,hl,hu⟩
    exact ⟨by linarith,by linarith,le_antisymm hu hl⟩
  · rintro ⟨h0,h1,rfl⟩
    exact ⟨⟨by linarith,by linarith⟩,le_rfl,le_rfl⟩

open FiniteGuardPieces in
/-- The generated operation guard removes zero while the original open boundary
at one stays absent, using exactly the existing finite-piece input description. -/
theorem open_piece_composition (t z : ℝ) :
    (∃x, x ∈ pieces openUnitBand t ∧ Admitted (RationalFamilyClosure.compile (.div .x .x)) x 0 ∧
      z = result (RationalFamilyClosure.compile (.div .x .x)) x 0) ↔
    0 < t ∧ t < 1 ∧ z=1 := by
  simp only [open_band]
  constructor
  · rintro ⟨x,⟨h0,h1,rfl⟩,hg,hz⟩
    have hn : x ≠ 0 := by simpa [Admitted,RationalFamilyClosure.compile,evalAt,MvPolynomial.coe_eval₂Hom] using hg
    have he : z=1 := by simpa [result,RationalFamilyClosure.compile,evalAt,MvPolynomial.coe_eval₂Hom,div_self hn] using hz
    exact ⟨lt_of_le_of_ne h0 (Ne.symm hn),h1,he⟩
  · rintro ⟨h0,h1,rfl⟩
    refine ⟨t,⟨h0.le,h1,rfl⟩,?_,?_⟩
    · simpa [Admitted,RationalFamilyClosure.compile,evalAt,MvPolynomial.coe_eval₂Hom] using ne_of_gt h0
    · simp [result,RationalFamilyClosure.compile,evalAt,MvPolynomial.coe_eval₂Hom,div_self (ne_of_gt h0)]

end GeneralizedIntervalArithmetic.RationalFamilyClosureChecks
#audit_namespace GeneralizedIntervalArithmetic.RationalFamilyClosureChecks
