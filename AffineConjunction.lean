import AffineUnary

namespace GeneralizedIntervalArithmetic.AffineConjunction

/-- Multiple bounds constrain the same value at the same parameter. This is an
intersection of enclosures, not a claim that any enclosed value is attainable. -/
def Contains (bounds : List LinearInterval) (t z : ℝ) : Prop :=
  ∀ I ∈ bounds, I.Contains t z

/-- None means no available bound. Contradictory available bounds are retained;
they must not be mistaken for an unavailable candidate and silently dropped. -/
def retain (ordinary : Option QInterval) (affine : Option LinearInterval) :
    Option (List LinearInterval) :=
  match ordinary, affine with
  | none, none => none
  | none, some A => some [A]
  | some B, none => some [.constant B]
  | some B, some A => some [.constant B, A]

theorem retain_nonempty {B A C} (h : retain B A = some C) : C ≠ [] := by
  cases B <;> cases A <;> simp_all [retain] <;> subst C <;> simp

theorem retain_sound {B A C} {t z : ℝ}
    (hb : ∀ J, B = some J → J.Contains z)
    (ha : ∀ J, A = some J → J.Contains t z)
    (hr : retain B A = some C) : Contains C t z := by
  cases B with
  | none =>
    cases A <;> simp_all [retain,Contains]
    subst C
    simp_all [Contains]
  | some B =>
    have hB := (linear_constant_contains B t z).mpr (hb B rfl)
    cases A <;> simp_all [retain,Contains] <;> subst C <;> simp_all [Contains]

/-- The old selected form is always one of the retained constraints. -/
theorem selected_mem {B A C O} (hc : retain B A = some C)
    (ho : AffineUnary.select B A = some O) : O ∈ C := by
  cases B with
  | none =>
    cases A <;> simp_all [retain,AffineUnary.select]
    subst C
    simp_all
  | some B =>
    cases A with
    | none =>
      simp_all [retain,AffineUnary.select]
      subst C
      simp_all
    | some A =>
      simp only [retain, Option.some.injEq] at hc
      subst C
      simp only [AffineUnary.select] at ho
      split at ho <;> cases ho <;> simp

theorem contained_in_selected {B A C O} (hc : retain B A = some C)
    (ho : AffineUnary.select B A = some O) {t z : ℝ} (hz : Contains C t z) :
    O.Contains t z := hz O (selected_mem hc ho)

theorem ordinary_preserved {B A C} (hc : retain (some B) A = some C)
    {t z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hz : Contains C t z) : B.Contains z := by
  obtain ⟨O,ho,hs⟩ := AffineUnary.ordinary_preserved B A
  exact hs t ht z (contained_in_selected hc ho hz)

/-- Reuse affine addition for every retained constraint at the same parameter. -/
def add (C : List LinearInterval) (J : LinearInterval) : List LinearInterval :=
  C.map (fun I => I.add J)

theorem add_sound {C J} {t x y : ℝ} (hx : Contains C t x) (hy : J.Contains t y) :
    Contains (add C J) t (x+y) := by
  intro K hK
  obtain ⟨I,hI,rfl⟩ := List.mem_map.mp hK
  exact linear_add_encloses (hx I hI) hy

theorem add_contained_in_selected {B A C O J} (hc : retain B A = some C)
    (ho : AffineUnary.select B A = some O) {t z : ℝ}
    (hz : Contains (add C J) t z) : (O.add J).Contains t z :=
  hz _ (List.mem_map.mpr ⟨O,selected_mem hc ho,rfl⟩)

def square (I : LinearInterval) : Option (List LinearInterval) :=
  retain (some (I.hull.mul I.hull)) (AffineUnary.squareCandidate I)

theorem square_available (I : LinearInterval) : ∃ C, square I = some C := by
  unfold square
  cases AffineUnary.squareCandidate I <;> exact ⟨_,rfl⟩

theorem square_sound {I C} (hc : square I = some C) {t x : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : I.Contains t x) : Contains C t (x^2) := by
  apply retain_sound ?_ ?_ hc
  · intro B hB
    cases hB
    simpa [pow_two] using mul_encloses (linear_hull_encloses ht hx) (linear_hull_encloses ht hx)
  · intro A hA
    exact AffineUnary.squareCandidate_sound hA ht hx

/-- Both the square and affine summand use this same actual input witness. -/
theorem square_add_image_sound {I C} (hc : square I = some C) (m c : ℚ)
    {t x : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : I.Contains t x) :
    Contains (add C (AffineUnary.image I m c)) t (x^2+((m:ℝ)*x+c)) :=
  add_sound (square_sound hc ht hx) (AffineUnary.image_sound m c ht hx)

/-- External restrictions stay in R. No existence follows from an enclosure. -/
def SquareAffineValues (R : ℝ → ℝ → Prop) (m c : ℚ) (t z : ℝ) : Prop :=
  ∃ x, R t x ∧ z = x^2+((m:ℝ)*x+c)

theorem relation_sound {I C} (hc : square I = some C) (m c : ℚ)
    {R : ℝ → ℝ → Prop}
    (hR : ∀ t x, R t x → t ∈ Set.Icc (0:ℝ) 1 ∧ I.Contains t x)
    {t z : ℝ} (hz : SquareAffineValues R m c t z) :
    Contains (add C (AffineUnary.image I m c)) t z := by
  obtain ⟨x,hx,rfl⟩ := hz
  exact square_add_image_sound hc m c (hR t x hx).1 (hR t x hx).2

theorem domain_iff (R : ℝ → ℝ → Prop) (m c : ℚ) (t : ℝ) :
    (∃ z, SquareAffineValues R m c t z) ↔ ∃ x, R t x := by
  constructor
  · rintro ⟨z,x,hx,_⟩; exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩; exact ⟨_,x,hx,rfl⟩

theorem exclusion_sound {C : List LinearInterval} {R : ℝ → ℝ → Prop} {t L U : ℝ}
    (hs : ∀ z, R t z → Contains C t z)
    (he : ∀ z, L ≤ z ∧ z ≤ U → ¬ Contains C t z) :
    ¬ ∃ z, R t z ∧ L ≤ z ∧ z ≤ U := by
  rintro ⟨z,hz,hw⟩
  exact he z hw (hs z hz)

end GeneralizedIntervalArithmetic.AffineConjunction
