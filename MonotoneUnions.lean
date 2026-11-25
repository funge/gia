import FractionalProjection
import MixedEndpoints
import Mathlib.Topology.Order.IntermediateValue

/-! Exact finite unions of branch images. Endpoint formulas require continuity
and strict monotonicity on the closed supporting interval, even for open ends. -/
namespace GeneralizedIntervalArithmetic.MonotoneUnions

/-- The same open/closed convention used by MixedEndpoints.bounds_nonempty. -/
def window (l u : ℝ) (lo hi : Bool) : Set ℝ :=
  {x | (if lo then l<x else l≤x) ∧ (if hi then x<u else x≤u)}

theorem window_subset (l u : ℝ) (lo hi : Bool) : window l u lo hi ⊆ Set.Icc l u := by
  cases lo <;> cases hi <;> intro x hx <;> simp only [window,Set.mem_setOf_eq,if_true,if_false,Bool.false_eq_true] at hx <;> constructor <;> linarith [hx.1,hx.2]

theorem window_nonempty (l u : ℝ) (lo hi : Bool) :
    (window l u lo hi).Nonempty ↔ l<u ∨ (l=u ∧ lo=false ∧ hi=false) :=
  MixedEndpoints.bounds_nonempty l u lo hi

theorem window_empty_of_reversed {l u : ℝ} (h : ¬l≤u) (lo hi : Bool) : window l u lo hi = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  have hh := window_subset l u lo hi hx
  exact h (hh.1.trans hh.2)

/-- Strict increase preserves each endpoint flag, including singleton controls. -/
theorem increasing_image {f : ℝ → ℝ} {l u : ℝ} (hlu : l≤u)
    (hc : ContinuousOn f (Set.Icc l u)) (hm : StrictMonoOn f (Set.Icc l u))
    (lo hi : Bool) : f '' window l u lo hi = window (f l) (f u) lo hi := by
  have hl : l ∈ Set.Icc l u := ⟨le_rfl,hlu⟩
  have hu : u ∈ Set.Icc l u := ⟨hlu,le_rfl⟩
  have compat (x : ℝ) (hx : x ∈ Set.Icc l u) :
      f x ∈ window (f l) (f u) lo hi ↔ x ∈ window l u lo hi := by
    cases lo <;> cases hi <;>
      simp [window,hm.lt_iff_lt hl hx,hm.lt_iff_lt hx hu,
        hm.le_iff_le hl hx,hm.le_iff_le hx hu]
  apply Set.Subset.antisymm
  · rintro z ⟨x,hx,rfl⟩
    exact (compat x (window_subset l u lo hi hx)).2 hx
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := intermediate_value_Icc hlu hc (window_subset (f l) (f u) lo hi hz)
    exact ⟨x,(compat x hx).1 hz,rfl⟩

/-- Strict decrease swaps endpoint values AND their open/closed flags. -/
theorem decreasing_image {f : ℝ → ℝ} {l u : ℝ} (hlu : l≤u)
    (hc : ContinuousOn f (Set.Icc l u)) (hm : StrictAntiOn f (Set.Icc l u))
    (lo hi : Bool) : f '' window l u lo hi = window (f u) (f l) hi lo := by
  have hl : l ∈ Set.Icc l u := ⟨le_rfl,hlu⟩
  have hu : u ∈ Set.Icc l u := ⟨hlu,le_rfl⟩
  have compat (x : ℝ) (hx : x ∈ Set.Icc l u) :
      f x ∈ window (f u) (f l) hi lo ↔ x ∈ window l u lo hi := by
    cases lo <;> cases hi <;>
      simp [window,hm.lt_iff_lt hu hx,hm.lt_iff_lt hx hl,
        hm.le_iff_le hu hx,hm.le_iff_le hx hl,and_comm]
  apply Set.Subset.antisymm
  · rintro z ⟨x,hx,rfl⟩
    exact (compat x (window_subset l u lo hi hx)).2 hx
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := intermediate_value_Icc' hlu hc (window_subset (f u) (f l) hi lo hz)
    exact ⟨x,(compat x hx).1 hz,rfl⟩

/-- Reversed inputs stay empty; endpoint reversal is not a repair of bad input. -/
def output (f : ℝ → ℝ) (l u : ℝ) (lo hi decreasing : Bool) : Set ℝ :=
  if l≤u then
    if decreasing then window (f u) (f l) hi lo else window (f l) (f u) lo hi
  else ∅

theorem branch_image (f : ℝ → ℝ) (l u : ℝ) (lo hi dec : Bool)
    (hc : l≤u → ContinuousOn f (Set.Icc l u))
    (hm : l≤u → if dec then StrictAntiOn f (Set.Icc l u) else StrictMonoOn f (Set.Icc l u)) :
    f '' window l u lo hi = output f l u lo hi dec := by
  by_cases h : l≤u
  · cases dec
    · simpa [output,h] using increasing_image h (hc h) (hm h) lo hi
    · simpa [output,h] using decreasing_image h (hc h) (hm h) lo hi
  · simp [output,h,window_empty_of_reversed h]

/-- A finite set of branch identifiers is retained before projecting its input.
Local exact graph-image results suffice; continuity is not presumed at poles. -/
theorem finite_projection {ι : Type*} (I : Finset ι) (G : ι → Prop)
    (S T : ι → Set ℝ) (R : ℝ → ℝ → Prop)
    (h : ∀i∈I, G i → ∀z, (∃x, x∈S i ∧ R x z) ↔ z∈T i) (z : ℝ) :
    (∃x, (∃i∈I, G i ∧ x∈S i) ∧ R x z) ↔ ∃i∈I, G i ∧ z∈T i := by
  constructor
  · rintro ⟨x,⟨i,hi,hg,hx⟩,hr⟩
    exact ⟨i,hi,hg,(h i hi hg z).1 ⟨x,hx,hr⟩⟩
  · rintro ⟨i,hi,hg,hz⟩
    obtain ⟨x,hx,hr⟩ := (h i hi hg z).2 hz
    exact ⟨x,⟨i,hi,hg,hx⟩,hr⟩

/-- Exact explicit output union, not a single interval hull. External guards
are retained with the very same branch. Apply pointwise for any parameter. -/
theorem finite_monotone_image {ι : Type*} (I : Finset ι) (G : ι → Prop)
    (f : ℝ → ℝ) (l u : ι → ℝ) (lo hi dec : ι → Bool)
    (hc : ∀i∈I, G i → l i≤u i → ContinuousOn f (Set.Icc (l i) (u i)))
    (hm : ∀i∈I, G i → l i≤u i →
      if dec i then StrictAntiOn f (Set.Icc (l i) (u i)) else StrictMonoOn f (Set.Icc (l i) (u i))) :
    f '' {x | ∃i∈I, G i ∧ x∈window (l i) (u i) (lo i) (hi i)} =
      {z | ∃i∈I, G i ∧ z∈output f (l i) (u i) (lo i) (hi i) (dec i)} := by
  ext z
  apply finite_projection I G _ _ (fun x z => f x=z)
  intro i hiMem hg z
  exact Set.ext_iff.mp (branch_image f (l i) (u i) (lo i) (hi i) (dec i)
    (hc i hiMem hg) (hm i hiMem hg)) z

/-- Reuse fractional-linear elimination for branches whose pole/asymptote makes
finite endpoint evaluation unsuitable. Original expression guards stay inside
Describes; no new literal-infinity arithmetic or continuity premise is added. -/
theorem finite_fractional_projection {ι : Type*} (I : Finset ι) (G : ι → Prop)
    (cs : ι → List FiniteGuardPieces.Piece) (e : Expr)
    (m : ι → FractionalProjection.Coefficients)
    (h : ∀i∈I, G i → FractionalProjection.Certified (m i) e) (t z : ℝ) :
    (∃x, (∃i∈I, G i ∧ x∈FiniteGuardPieces.pieces (cs i) t) ∧ Value x t e z) ↔
      ∃i∈I, G i ∧ FractionalProjection.Describes (m i) (cs i) e t z := by
  apply finite_projection I G _ _ (fun x z => Value x t e z)
  intro i hi hg z
  exact FractionalProjection.projection_exact (h i hi hg) (cs i) t z

theorem square_increasing {l u : ℝ} (hl : 0≤l) :
    StrictMonoOn (fun x : ℝ => x^2) (Set.Icc l u) := by
  intro x hx y hy hxy
  change x^2 < y^2
  have hsum : 0<x+y := by linarith [hx.1,hy.1]
  nlinarith [mul_pos (sub_pos.mpr hxy) hsum]

theorem square_decreasing {l u : ℝ} (hu : u≤0) :
    StrictAntiOn (fun x : ℝ => x^2) (Set.Icc l u) := by
  intro x hx y hy hxy
  change y^2 < x^2
  have hsum : x+y<0 := by linarith [hx.2,hy.2]
  nlinarith [mul_pos_of_neg_of_neg (sub_neg.mpr hxy) hsum]

/-- Both branches are necessary for a general input crossing zero. The union
retains exact membership; it is allowed to overlap at the shared zero output. -/
theorem square_crossing {l u : ℝ} (hl : l≤0) (hu : 0≤u) :
    (fun x : ℝ => x^2) '' Set.Icc l u = Set.Icc 0 (l^2) ∪ Set.Icc 0 (u^2) := by
  have hs : Set.Icc l u = window l 0 false false ∪ window 0 u false false := by
    ext x
    simp only [window,Set.mem_Icc,Set.mem_union,Set.mem_setOf_eq,Bool.false_eq_true,if_false]
    constructor
    · intro hx; rcases le_total x 0 with h | h
      · exact Or.inl ⟨hx.1,h⟩
      · exact Or.inr ⟨h,hx.2⟩
    · rintro (hx | hx) <;> constructor <;> linarith [hx.1,hx.2]
  rw [hs,Set.image_union,decreasing_image hl (by fun_prop) (square_decreasing le_rfl),
    increasing_image hu (by fun_prop) (square_increasing le_rfl)]
  simp [window,Set.Icc]

/-- Rational constant endpoints use the existing piece code, including openness. -/
def encode (l u : ℚ) (lo hi : Bool) : List FiniteGuardPieces.Piece :=
  (FiniteGuardPieces.band [] ⟨l,l⟩ ⟨u,u⟩ lo hi).compile

theorem encode_exact (l u : ℚ) (lo hi : Bool) (t : ℝ) :
    FiniteGuardPieces.pieces (encode l u lo hi) t = window (l:ℝ) (u:ℝ) lo hi := by
  have hv (q : ℚ) : (⟨q,q⟩ : QAffine).value t = (q:ℝ) := by unfold QAffine.value; ring
  ext z
  simp [encode,FiniteGuardPieces.band_exact,FiniteGuardPieces.guardHolds,hv,window]

theorem split_zero {l u : ℝ} (hl : l<0) (hu : 0<u) (lo hi : Bool) :
    window l u lo hi = window l 0 lo false ∪ window 0 u false hi := by
  cases lo <;> cases hi <;> ext x <;>
    simp only [window,Set.mem_setOf_eq,Set.mem_union,if_true,if_false,Bool.false_eq_true]
  all_goals
    constructor
    · intro hx
      rcases le_total x 0 with h | h
      · left; constructor <;> linarith [hx.1,hx.2]
      · right; constructor <;> linarith [hx.1,hx.2]
    · rintro (hx | hx) <;> constructor <;> linarith [hx.1,hx.2]

/-- Exact rational output-piece construction for square, not a hull. Interior
zero is included on both branches; original exterior flags are retained. -/
def squarePieces (l u : ℚ) (lo hi : Bool) : List FiniteGuardPieces.Piece :=
  if l≤u then
    if u≤0 then encode (u^2) (l^2) hi lo
    else if 0≤l then encode (l^2) (u^2) lo hi
    else encode 0 (l^2) false lo ++ encode 0 (u^2) false hi
  else []

theorem square_pieces_exact (l u : ℚ) (lo hi : Bool) (t : ℝ) :
    FiniteGuardPieces.pieces (squarePieces l u lo hi) t =
      (fun x : ℝ => x^2) '' window (l:ℝ) (u:ℝ) lo hi := by
  by_cases hlu : l≤u
  · have hlu' : (l:ℝ)≤u := by exact_mod_cast hlu
    by_cases hu : u≤0
    · have hu' : (u:ℝ)≤0 := by exact_mod_cast hu
      rw [squarePieces,if_pos hlu,if_pos hu,encode_exact]
      simpa using (decreasing_image hlu' (by fun_prop) (square_decreasing hu') lo hi).symm
    · by_cases hl : 0≤l
      · have hl' : (0:ℝ)≤l := by exact_mod_cast hl
        rw [squarePieces,if_pos hlu,if_neg hu,if_pos hl,encode_exact]
        simpa using (increasing_image hlu' (by fun_prop) (square_increasing hl') lo hi).symm
      · have hl' : (l:ℝ)<0 := by exact_mod_cast lt_of_not_ge hl
        have hu' : (0:ℝ)<u := by exact_mod_cast lt_of_not_ge hu
        rw [squarePieces,if_pos hlu,if_neg hu,if_neg hl,FiniteGuardPieces.pieces_append,
          encode_exact,encode_exact,split_zero hl' hu',Set.image_union,
          decreasing_image hl'.le (by fun_prop) (square_decreasing le_rfl),
          increasing_image hu'.le (by fun_prop) (square_increasing le_rfl)]
        simp
  · have hlu' : ¬(l:ℝ)≤u := by exact_mod_cast hlu
    simp [squarePieces,hlu,window_empty_of_reversed hlu',FiniteGuardPieces.pieces,
      IntervalSetDenotation.denote]

/-- Match the existing expression semantics; no occurrence gets a fresh input. -/
theorem square_expression (x y z : ℝ) : Value x y (.mul .x .x) z ↔ z=x^2 := by
  constructor
  · intro h; cases h with
    | mul h1 h2 => cases h1; cases h2; ring
  · rintro rfl
    simpa [pow_two] using Value.mul (Value.x (x:=x) (y:=y)) (Value.x (x:=x) (y:=y))

theorem square_piece_expression (l u : ℚ) (lo hi : Bool) (t y z : ℝ) :
    z ∈ FiniteGuardPieces.pieces (squarePieces l u lo hi) t ↔
      ∃x, x∈window (l:ℝ) (u:ℝ) lo hi ∧ Value x y (.mul .x .x) z := by
  rw [square_pieces_exact]
  simp [square_expression,eq_comm]

/-- Parameter-only guards remain explicit in the emitted output pieces. -/
def guardedSquares (g : FiniteGuardPieces.Guard) (l u : ℚ) (lo hi : Bool) :
    List FiniteGuardPieces.Piece :=
  FiniteGuardPieces.meet [FiniteGuardPieces.guardAtoms g] (squarePieces l u lo hi)

theorem guarded_square_exact (g : FiniteGuardPieces.Guard) (l u : ℚ) (lo hi : Bool) (t y z : ℝ) :
    z ∈ FiniteGuardPieces.pieces (guardedSquares g l u lo hi) t ↔
      FiniteGuardPieces.guardHolds g t ∧ ∃x, x∈window (l:ℝ) (u:ℝ) lo hi ∧ Value x y (.mul .x .x) z := by
  rw [guardedSquares,FiniteGuardPieces.meet_exact]
  simp only [Set.mem_inter_iff,square_piece_expression l u lo hi t y z]
  have hg : z ∈ FiniteGuardPieces.pieces [FiniteGuardPieces.guardAtoms g] t ↔
      FiniteGuardPieces.guardHolds g t := by
    simp [FiniteGuardPieces.pieces,IntervalSetDenotation.denote,FiniteGuardPieces.guard_exact]
  rw [hg]

end GeneralizedIntervalArithmetic.MonotoneUnions
