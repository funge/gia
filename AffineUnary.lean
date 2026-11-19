import TangentBounds
import LinearMultiplication
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace GeneralizedIntervalArithmetic.AffineUnary

/-- Reuse existing affine multiplication/addition, including coefficient signs. -/
def image (I : LinearInterval) (m c : ℚ) : LinearInterval :=
  (I.mul (.constant (.point m))).add (.constant (.point c))

theorem image_sound {I : LinearInterval} {t x : ℝ} (m c : ℚ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : I.Contains t x) :
    (image I m c).Contains t ((m:ℝ)*x+c) := by
  have hp (q : ℚ) : (LinearInterval.constant (.point q)).Contains t (q:ℝ) :=
    (linear_constant_contains _ _ _).mpr ⟨le_rfl,le_rfl⟩
  simpa [image,mul_comm] using linear_add_encloses (linear_mul_encloses ht hx (hp m)) (hp c)

/-- Assemble the lower side of one affine image and upper side of another.
Failure is unknown: it supplies neither a range nor a domain classification. -/
def propagate (I : LinearInterval) (lm lc um uc : ℚ) : Option LinearInterval :=
  let L := (image I lm lc).lower
  let U := (image I um uc).upper
  if h : L.atZero ≤ U.atZero ∧ L.atOne ≤ U.atOne then
    some ⟨L,U,h.1,h.2⟩ else none

/-- A relational unary operation may be partial. Only actual related values
are enclosed; no use of a totalized operation is hidden in this contract. -/
theorem propagate_sound {I O : LinearInterval} {lm lc um uc : ℚ}
    {F : ℝ → ℝ → Prop}
    (hF : ∀ x z, I.hull.Contains x → F x z →
      (lm:ℝ)*x+lc ≤ z ∧ z ≤ (um:ℝ)*x+uc)
    (hr : propagate I lm lc um uc = some O)
    {t x z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : I.Contains t x) (hz : F x z) :
    O.Contains t z := by
  have hs := hF x z (linear_hull_encloses ht hx) hz
  have hl := image_sound lm lc ht hx
  have hu := image_sound um uc ht hx
  dsimp only [propagate] at hr
  split at hr
  · cases Option.some.inj hr
    exact ⟨hl.1.trans hs.1,hs.2.trans hu.2⟩
  · cases hr

/-- Preserve affine structure only when its whole hull fits in the ordinary
result. Otherwise keep that ordinary result, embedded as a constant form. -/
def select (ordinary : Option QInterval) (affine : Option LinearInterval) : Option LinearInterval :=
  match ordinary,affine with
  | none,A => A
  | some B,none => some (.constant B)
  | some B,some A =>
      if B.lo ≤ A.hull.lo ∧ A.hull.hi ≤ B.hi then some A else some (.constant B)

theorem select_sound {B : Option QInterval} {A : Option LinearInterval} {O : LinearInterval}
    {t z : ℝ} (hb : ∀ J, B = some J → J.Contains z)
    (ha : ∀ J, A = some J → J.Contains t z) (hr : select B A = some O) : O.Contains t z := by
  cases B with
  | none => exact ha O hr
  | some B => cases A with
    | none => cases hr; exact (linear_constant_contains _ _ _).mpr (hb B rfl)
    | some A =>
      simp only [select] at hr
      split at hr
      · cases hr; exact ha _ rfl
      · cases hr; exact (linear_constant_contains _ _ _).mpr (hb B rfl)

theorem ordinary_preserved (B : QInterval) (A : Option LinearInterval) :
    ∃ O, select (some B) A = some O ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z, O.Contains t z → B.Contains z := by
  cases A with
  | none => exact ⟨.constant B,rfl,fun t _ z h => (linear_constant_contains B t z).mp h⟩
  | some A =>
    simp only [select]
    split
    · rename_i h
      refine ⟨A,rfl,?_⟩
      intro t ht z hz
      have hh := linear_hull_encloses ht hz
      exact ⟨(by exact_mod_cast h.1 : (B.lo:ℝ) ≤ A.hull.lo).trans hh.1,
        hh.2.trans (by exact_mod_cast h.2)⟩
    · exact ⟨.constant B,rfl,fun t _ z h => (linear_constant_contains B t z).mp h⟩

/-- The same input witness supplies the output value; external holes are retained. -/
def UnaryValues (R : ℝ → ℝ → Prop) (F : ℝ → ℝ → Prop) (t z : ℝ) : Prop :=
  ∃ x, R t x ∧ F x z

theorem domain_sound {I O : LinearInterval} {D : DomainBounds ℝ}
    {R F : ℝ → ℝ → Prop} (hI : (I.onDomain D).Sound R)
    (hout : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x z, I.Contains t x → F x z → O.Contains t z)
    (hdefined : ∀ x, I.hull.Contains x → ∃ z, F x z) :
    (O.onDomain D).Sound (UnaryValues R F) := by
  refine ⟨?_,?_,?_⟩
  · rintro t z ⟨x,hx,hz⟩
    exact hout t (hI.2.1 t x hx).1 x z (hI.1 t x hx) hz
  · rintro t z ⟨x,hx,_⟩
    exact hI.2.1 t x hx
  · intro t ht
    obtain ⟨x,hx⟩ := hI.2.2 t ht
    obtain ⟨z,hz⟩ := hdefined x (linear_hull_encloses ht.1 (hI.1 t x hx))
    exact ⟨z,x,hx,hz⟩

/-- Square's supporting tangent at a and exact endpoint chord on [a,b].
This uses the merged tangent/chord theory, including the singleton case. -/
theorem square_support {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    2*a*x-a^2 ≤ x^2 ∧ x^2 ≤ (a+b)*x-a*b := by
  have hab := hx.1.trans hx.2
  have hf : ConvexOn ℝ (Set.Icc a b) (fun x : ℝ => x^2) :=
    (Even.convexOn_pow (by decide : Even 2)).subset (fun _ _ => Set.mem_univ _) (convex_Icc _ _)
  have hd : HasDerivAt (fun x : ℝ => x^2) (2*a) a := by
    convert (hasDerivAt_id a).pow 2 using 1; norm_num
  have hl := TangentBounds.convex_lower hf ⟨le_rfl,hab⟩ hd.hasDerivWithinAt hx
  obtain ⟨t,ht,he⟩ := EndpointChords.parameter_exists hx
  have hu := EndpointChords.convex_upper hab hf ht
  have chord : EndpointChords.blend (a^2) (b^2) t =
      (a+b)*EndpointChords.blend a b t-a*b := by dsimp [EndpointChords.blend]; ring
  rw [chord,he] at hu
  exact ⟨by dsimp [TangentBounds.tangent] at hl; nlinarith,hu⟩

def squareCandidate (I : LinearInterval) : Option LinearInterval :=
  let a := I.hull.lo
  let b := I.hull.hi
  propagate I (2*a) (-(a^2)) (a+b) (-(a*b))

/-- Ordinary multiplication is an intentionally conservative baseline for square. -/
def square (I : LinearInterval) : Option LinearInterval :=
  select (some (I.hull.mul I.hull)) (squareCandidate I)

theorem squareCandidate_sound {I O : LinearInterval} (hr : squareCandidate I = some O)
    {t x : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : I.Contains t x) : O.Contains t (x^2) := by
  apply propagate_sound (F := fun x z => z=x^2) ?_ hr ht hx rfl
  intro y z hy hz
  subst z
  have h := square_support hy
  push_cast
  constructor <;> linarith [h.1,h.2]

theorem square_sound {I O : LinearInterval} (hr : square I = some O)
    {t x : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : I.Contains t x) : O.Contains t (x^2) := by
  apply select_sound ?_ ?_ hr
  · intro B hB
    cases hB
    simpa [pow_two] using mul_encloses (linear_hull_encloses ht hx) (linear_hull_encloses ht hx)
  · intro A hA
    exact squareCandidate_sound hA ht hx

theorem square_preserves_ordinary (I : LinearInterval) :
    ∃ O, square I = some O ∧ ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z,
      O.Contains t z → (I.hull.mul I.hull).Contains z := ordinary_preserved _ _

theorem square_domain_sound {I O : LinearInterval} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} (hI : (I.onDomain D).Sound R) (hr : square I = some O) :
    (O.onDomain D).Sound (UnaryValues R (fun x z => z=x^2)) := by
  refine domain_sound (F := fun x z => z=x^2) hI ?_ ?_
  · intro t ht x z hx hz
    subst z
    exact square_sound hr ht hx
  · intro x _
    exact ⟨x^2,rfl⟩

end GeneralizedIntervalArithmetic.AffineUnary
