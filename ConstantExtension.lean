import GeneralFamilyDemotion

/-! Conditional semantic counterpart of Tupper §2.9.4. Bounds are functions
into EReal; infinite bounds do not become literal infinite output values.
The compatibility premises concern demoters, not the operator equality proved. -/
namespace GeneralizedIntervalArithmetic.ConstantExtension
open GeneralFamilyDemotion

abbrev Bounds (P : Type*) := (P → EReal) × (P → EReal)
noncomputable def constant {P : Type*} (b : EReal × EReal) : Bounds P :=
  (fun _ => b.1,fun _ => b.2)

theorem constant_injective {P : Type*} [Nonempty P] :
    Function.Injective (constant (P:=P)) := by
  intro a b h
  obtain ⟨p⟩ := ‹Nonempty P›
  exact Prod.ext (congrArg (fun c => c.1 p) h) (congrArg (fun c => c.2 p) h)

/-- Outward lower bounds that dominate every admissible constant lower bound. -/
def LowerCompatible {P : Type*} (down : (P → EReal) → P → EReal) : Prop :=
  (∀ f p, down f p ≤ f p) ∧
    ∀ f c, (∀ p, c ≤ f p) → ∀ p, c ≤ down f p

/-- Dual compatibility with constant upper competitors. Not global affine optimality. -/
def UpperCompatible {P : Type*} (up : (P → EReal) → P → EReal) : Prop :=
  (∀ f p, f p ≤ up f p) ∧
    ∀ f c, (∀ p, f p ≤ c) → ∀ p, up f p ≤ c

theorem lower_fixes_constants {P : Type*} {down : (P → EReal) → P → EReal}
    (h : LowerCompatible down) (c : EReal) : down (fun _ => c) = fun _ => c := by
  funext p
  exact le_antisymm (h.1 _ p) (h.2 _ c (fun _ => le_rfl) p)

theorem upper_fixes_constants {P : Type*} {up : (P → EReal) → P → EReal}
    (h : UpperCompatible up) (c : EReal) : up (fun _ => c) = fun _ => c := by
  funext p
  exact le_antisymm (h.2 _ c (fun _ => le_rfl) p) (h.1 (fun _ => c) p)

/-- Constructed witnesses: infimum/supremum constant projections satisfy the
premises. No extremal values need be attained or computable. -/
noncomputable def projectDown {P : Type*} (f : P → EReal) : P → EReal :=
  fun _ => sInf (Set.range f)
noncomputable def projectUp {P : Type*} (f : P → EReal) : P → EReal :=
  fun _ => sSup (Set.range f)

theorem projectDown_compatible {P : Type*} : LowerCompatible (projectDown (P:=P)) := by
  constructor
  · intro f p; exact sInf_le ⟨p,rfl⟩
  · intro f c h p; exact le_sInf (by rintro _ ⟨q,rfl⟩; exact h q)

theorem projectUp_compatible {P : Type*} : UpperCompatible (projectUp (P:=P)) := by
  constructor
  · intro f p; exact le_sSup ⟨p,rfl⟩
  · intro f c h p; exact sSup_le (by rintro _ ⟨q,rfl⟩; exact h q)

/-- Scalar interval extension from actual outputs of an arbitrary partial relation. -/
noncomputable def scalar {W : Type*} (A : W → Prop) (G : W → ℝ → Prop) : EReal × EReal :=
  let S := outputs (fun (_ : Unit) => A) (fun _ => G) ()
  (ExtendedImageHull.lower S, ExtendedImageHull.upper S)

/-- Pointwise interval extension followed by the two endpoint demoters. -/
noncomputable def family {P W : Type*}
    (down up : (P → EReal) → P → EReal) (A : P → W → Prop)
    (G : W → ℝ → Prop) : Bounds P :=
  (down (fun p => ExtendedImageHull.lower (outputs A (fun _ => G) p)),
   up (fun p => ExtendedImageHull.upper (outputs A (fun _ => G) p)))

/-- Generic homomorphism equation, derived from independently checkable demotion
premises. W retains any correlation/partial guards; no Cartesian product is forced. -/
theorem constant_extension {P W : Type*}
    {down up : (P → EReal) → P → EReal}
    (hl : LowerCompatible down) (hu : UpperCompatible up)
    (A : W → Prop) (G : W → ℝ → Prop) :
    family down up (fun _ => A) G = constant (P:=P) (scalar A G) := by
  simp only [family,scalar,constant,outputs]
  exact Prod.ext (lower_fixes_constants hl _) (upper_fixes_constants hu _)

/-- Source n-ary interval case. Partiality is in G, including a nonzero guard
if G denotes division. The same tuple is used in every operation predicate. -/
theorem nary_extension {P : Type*} {n : ℕ}
    {down up : (P → EReal) → P → EReal}
    (hl : LowerCompatible down) (hu : UpperCompatible up)
    (J : Fin n → Set ℝ) (G : (Fin n → ℝ) → ℝ → Prop) :
    family down up (fun _ x => ∀ i, x i ∈ J i) G =
      constant (P:=P) (scalar (fun x => ∀ i, x i ∈ J i) G) :=
  constant_extension hl hu _ _

/-- The literal commuting diagram for constant endpoint pairs and arbitrary
finite-arity partial real operations. This is equality of represented bound
functions, not automatically of redundant coefficient syntax. -/
theorem interval_homomorphism {P : Type*} {n : ℕ}
    {down up : (P → EReal) → P → EReal}
    (hl : LowerCompatible down) (hu : UpperCompatible up)
    (I : Fin n → EReal × EReal) (G : (Fin n → ℝ) → ℝ → Prop) :
    family down up (fun p x => ∀ i, x i ∈ ExtendedImageHull.interval
      ((constant (P:=P) (I i)).1 p) ((constant (P:=P) (I i)).2 p)) G =
    constant (P:=P) (scalar (fun x => ∀ i,
      x i ∈ ExtendedImageHull.interval (I i).1 (I i).2) G) := by
  simpa only [constant] using constant_extension hl hu
    (fun x : Fin n → ℝ => ∀ i, x i ∈ ExtendedImageHull.interval (I i).1 (I i).2) G

/-- Soundness of the family result, without the constant-input restriction. -/
theorem family_encloses {P W : Type*} {down up : (P → EReal) → P → EReal}
    (hl : LowerCompatible down) (hu : UpperCompatible up)
    (A : P → W → Prop) (G : W → ℝ → Prop) {p w z}
    (ha : A p w) (hg : G w z) :
    z ∈ ExtendedImageHull.interval ((family down up A G).1 p) ((family down up A G).2 p) := by
  have h := ExtendedImageHull.sound (outputs A (fun _ => G) p) ⟨w,ha,hg⟩
  exact ⟨(hl.1 _ p).trans h.1,h.2.trans (hu.1 (fun q => ExtendedImageHull.upper (outputs A (fun _ => G) q)) p)⟩

end GeneralizedIntervalArithmetic.ConstantExtension
