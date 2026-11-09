import ConditionalCovers

namespace GeneralizedIntervalArithmetic

/-- Pair every component at the same parameter. This retains all possible
operand choices, but does not infer correlation between their witnesses. -/
def FiniteLinearCover.mul (A B : FiniteLinearCover) : FiniteLinearCover :=
  A.flatMap (fun I => B.map (fun J => I.mul J))

theorem cover_mul_member {A B : FiniteLinearCover} {K : LinearInterval} :
    K ∈ A.mul B ↔ ∃ I ∈ A, ∃ J ∈ B, I.mul J = K := by
  simp [FiniteLinearCover.mul,List.mem_flatMap,List.mem_map]

theorem cover_mul_length (A B : FiniteLinearCover) :
    (A.mul B).length = A.length * B.length := by
  induction A with
  | nil => simp [FiniteLinearCover.mul]
  | cons I A ih => simpa [FiniteLinearCover.mul,Nat.add_mul,Nat.add_comm] using ih

/-- All pairs are needed for arbitrary relations; pairing corresponding list
positions would lose actual products. -/
theorem cover_mul_sound {A B : FiniteLinearCover} {R S : ℝ → ℝ → Prop}
    (ha : A.Covers R) (hb : B.Covers S) :
    (A.mul B).Covers (ProductValues R S) := by
  rintro t ht z ⟨x,y,hx,hy,rfl⟩
  obtain ⟨I,hi,hx⟩ := ha t ht x hx
  obtain ⟨J,hj,hy⟩ := hb t ht y hy
  exact ⟨I.mul J,cover_mul_member.mpr ⟨I,hi,J,hj,rfl⟩,
    linear_mul_encloses ht hx hy⟩

/-- Multiplication is total on real values, so both domain directions use the
existing intersection; no new domain predicate or existence premise is needed. -/
theorem cover_mul_domain_sound {A B : FiniteLinearCover} {D E : DomainBounds ℝ}
    {R S : ℝ → ℝ → Prop} (ha : A.SoundOn D R) (hb : B.SoundOn E S) :
    (A.mul B).SoundOn (D.inter E) (ProductValues R S) := by
  refine ⟨?_,?_,?_⟩
  · rintro t z ⟨x,y,hx,hy,rfl⟩
    exact cover_mul_sound (cover_soundOn_covers ha) (cover_soundOn_covers hb)
      t (ha.2.1 t x hx).1 (x*y) ⟨x,y,hx,hy,rfl⟩
  · rintro t z ⟨x,y,hx,hy,_⟩
    exact ⟨(ha.2.1 t x hx).1,(ha.2.1 t x hx).2,(hb.2.1 t y hy).2⟩
  · intro t ht
    obtain ⟨x,hx⟩ := ha.2.2 t ⟨ht.1,ht.2.1⟩
    obtain ⟨y,hy⟩ := hb.2.2 t ⟨ht.1,ht.2.2⟩
    exact ⟨x*y,x,y,hx,hy,rfl⟩

/-- One actual input witness, used twice. This differs from ProductValues R R
when R is multivalued. -/
def SquareValues {α : Type*} (R : α → ℝ → Prop) (p : α) (z : ℝ) : Prop :=
  ∃ x, R p x ∧ z = x*x

/-- Keep only self-products of components for the shared-witness square relation.
Within-component overestimation remains that of the existing multiplication. -/
def FiniteLinearCover.square (A : FiniteLinearCover) : FiniteLinearCover :=
  A.map (fun I => I.mul I)

theorem cover_square_member {A : FiniteLinearCover} {K : LinearInterval} :
    K ∈ A.square ↔ ∃ I ∈ A, I.mul I = K := by
  simp [FiniteLinearCover.square]

theorem cover_square_length (A : FiniteLinearCover) : A.square.length = A.length := by
  simp [FiniteLinearCover.square]

theorem cover_square_member_mul {A : FiniteLinearCover} {K : LinearInterval}
    (h : K ∈ A.square) : K ∈ A.mul A := by
  obtain ⟨I,hi,rfl⟩ := cover_square_member.mp h
  exact cover_mul_member.mpr ⟨I,hi,I,hi,rfl⟩

theorem cover_square_sound {A : FiniteLinearCover} {R : ℝ → ℝ → Prop}
    (ha : A.Covers R) : A.square.Covers (SquareValues R) := by
  rintro t ht z ⟨x,hx,rfl⟩
  obtain ⟨I,hi,hx⟩ := ha t ht x hx
  exact ⟨I.mul I,cover_square_member.mpr ⟨I,hi,rfl⟩,
    linear_mul_encloses ht hx hx⟩

theorem cover_square_domain_sound {A : FiniteLinearCover} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} (ha : A.SoundOn D R) : A.square.SoundOn D (SquareValues R) := by
  refine ⟨?_,?_,?_⟩
  · rintro t z ⟨x,hx,rfl⟩
    exact cover_square_sound (cover_soundOn_covers ha) t (ha.2.1 t x hx).1
      (x*x) ⟨x,hx,rfl⟩
  · rintro t z ⟨x,hx,_⟩
    exact ha.2.1 t x hx
  · intro t ht
    obtain ⟨x,hx⟩ := ha.2.2 t ht
    exact ⟨x*x,x,hx,rfl⟩

/-- Independent and shared choices agree when the input is single-valued.
No single-valuedness is required by the square enclosure theorem itself. -/
theorem squareValues_iff_product_self {α : Type*} {R : α → ℝ → Prop}
    (hu : ∀ p x y, R p x → R p y → x = y) (p : α) (z : ℝ) :
    SquareValues R p z ↔ ProductValues R R p z := by
  constructor
  · rintro ⟨x,hx,hz⟩
    exact ⟨x,x,hx,hx,hz⟩
  · rintro ⟨x,y,hx,hy,hz⟩
    obtain rfl := hu p x y hx hy
    exact ⟨x,hx,hz⟩

end GeneralizedIntervalArithmetic
