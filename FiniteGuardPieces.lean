import IntervalSetDenotation
import TaggedConversion
import LinearIntervals

/-! A deliberately restricted finite code for §§2.13–2.14's set semantics.
This grammar is an implementation choice, not a transcription of source syntax. -/
namespace GeneralizedIntervalArithmetic.FiniteGuardPieces

/-- Rational affine half-space in the shared parameter and output value.
`strict` distinguishes an open boundary from a closed boundary. -/
structure Atom where
  parameter : ℚ
  output : ℚ
  constant : ℚ
  strict : Bool
  deriving DecidableEq, Repr

def Atom.Holds (a : Atom) (t z : ℝ) : Prop :=
  if a.strict then a.parameter * t + a.output * z + a.constant < 0
  else a.parameter * t + a.output * z + a.constant ≤ 0

def Atom.test (a : Atom) (t z : ℚ) : Bool :=
  if a.strict then decide (a.parameter * t + a.output * z + a.constant < 0)
  else decide (a.parameter * t + a.output * z + a.constant ≤ 0)

theorem atom_test_exact (a : Atom) (t z : ℚ) :
    a.test t z = true ↔ a.Holds (t:ℝ) (z:ℝ) := by
  cases a with
  | mk p q c strict =>
    cases strict <;> simp only [Atom.test,Atom.Holds,Bool.false_eq_true,if_false,if_true,
      decide_eq_true_eq] <;> norm_cast

abbrev Piece := List Atom

def piece (c : Piece) (t : ℝ) : Set ℝ := {z | ∀ a ∈ c, a.Holds t z}
def pieces (cs : List Piece) (t : ℝ) : Set ℝ :=
  IntervalSetDenotation.denote piece {c | c ∈ cs} t

def test (cs : List Piece) (t z : ℚ) : Bool :=
  cs.any (fun c => c.all (fun a => a.test t z))

theorem test_exact (cs : List Piece) (t z : ℚ) :
    test cs t z = true ↔ (z:ℝ) ∈ pieces cs (t:ℝ) := by
  simp [test,pieces,IntervalSetDenotation.denote,piece,atom_test_exact]

/-- Union is concatenation; intersection distributes into pairs of pieces. -/
def meet (cs ds : List Piece) : List Piece :=
  cs.flatMap (fun c => ds.map (fun d => c ++ d))

theorem piece_append (c d : Piece) (t : ℝ) :
    piece (c ++ d) t = piece c t ∩ piece d t := by
  ext z
  simp [piece,or_imp,forall_and]

theorem pieces_append (cs ds : List Piece) (t : ℝ) :
    pieces (cs ++ ds) t = pieces cs t ∪ pieces ds t := by
  ext z
  simp [pieces,IntervalSetDenotation.denote,List.mem_append]
  aesop

theorem meet_exact (cs ds : List Piece) (t : ℝ) :
    pieces (meet cs ds) t = pieces cs t ∩ pieces ds t := by
  ext z
  simp only [pieces,IntervalSetDenotation.denote,Set.mem_setOf_eq,meet,
    List.mem_flatMap,List.mem_map,Set.mem_inter_iff]
  constructor
  · rintro ⟨_,⟨c,hc,d,hd,rfl⟩,hz⟩
    rw [piece_append] at hz
    exact ⟨⟨c,hc,hz.1⟩,⟨d,hd,hz.2⟩⟩
  · rintro ⟨⟨c,hc,hz⟩,⟨d,hd,hw⟩⟩
    exact ⟨c++d,⟨c,hc,d,hd,rfl⟩,by rw [piece_append]; exact ⟨hz,hw⟩⟩

inductive Description where
  | empty
  | cell (c : Piece)
  | union (a b : Description)
  | inter (a b : Description)
  deriving DecidableEq, Repr

def Description.denote : Description → ℝ → Set ℝ
  | .empty, _ => ∅
  | .cell c, t => piece c t
  | .union a b, t => a.denote t ∪ b.denote t
  | .inter a b, t => a.denote t ∩ b.denote t

def Description.compile : Description → List Piece
  | .empty => []
  | .cell c => [c]
  | .union a b => a.compile ++ b.compile
  | .inter a b => meet a.compile b.compile

/-- Exact compilation, including empty pieces and shared boundary witnesses.
No parameter or output existential is independently projected during compilation. -/
theorem compile_exact (D : Description) (t : ℝ) :
    pieces D.compile t = D.denote t := by
  induction D with
  | empty => ext z; simp [Description.compile,Description.denote,pieces,IntervalSetDenotation.denote]
  | cell c => ext z; simp [Description.compile,Description.denote,pieces,IntervalSetDenotation.denote]
  | union a b ha hb => simp [Description.compile,Description.denote,pieces_append,ha,hb]
  | inter a b ha hb => simp [Description.compile,Description.denote,meet_exact,ha,hb]

theorem compiled_test_exact (D : Description) (t z : ℚ) :
    test D.compile t z = true ↔ (z:ℝ) ∈ D.denote (t:ℝ) := by
  rw [test_exact,compile_exact]

/-- Restricting the external parameter domain commutes with compilation. -/
theorem restricted_exact (A : Set ℝ) (D : Description) (t z : ℝ) :
    (t ∈ A ∧ z ∈ pieces D.compile t) ↔ t ∈ A ∧ z ∈ D.denote t := by
  rw [compile_exact]

theorem empty_fiber (D : Description) (t : ℝ) :
    pieces D.compile t = ∅ ↔ D.denote t = ∅ := by rw [compile_exact]

/-- Exact finite re-encoding also leaves all three exceptional tags untouched.
It does not create a numerical meaning for any exceptional arithmetic operation. -/
theorem tagged_exact (D : Description) (t : ℝ) (S : Set ExceptionalComparisons.Value) :
    TaggedConversion.lift (fun _ => pieces D.compile t) S =
      TaggedConversion.lift (fun _ => D.denote t) S := by rw [compile_exact]

/-- Encode an affine endpoint comparison directly into the shared (t,z) plane. -/
def lower (a : QAffine) (strict : Bool) : Atom :=
  ⟨a.atOne-a.atZero,-1,a.atZero,strict⟩
def upper (a : QAffine) (strict : Bool) : Atom :=
  ⟨a.atZero-a.atOne,1,-a.atZero,strict⟩

theorem lower_exact (a : QAffine) (s : Bool) (t z : ℝ) :
    (lower a s).Holds t z ↔ if s then a.value t < z else a.value t ≤ z := by
  cases s <;> simp [lower,Atom.Holds,QAffine.value] <;>
    constructor <;> intro h <;> nlinarith

theorem upper_exact (a : QAffine) (s : Bool) (t z : ℝ) :
    (upper a s).Holds t z ↔ if s then z < a.value t else z ≤ a.value t := by
  cases s <;> simp [upper,Atom.Holds,QAffine.value] <;>
    constructor <;> intro h <;> nlinarith

/-- Parameter guards cannot silently inspect or choose an independent output. -/
abbrev Guard := List (QAffine × Bool)
def guardAtoms (g : Guard) : Piece := g.map (fun (a,s) =>
  ⟨a.atOne-a.atZero,0,a.atZero,s⟩)
def guardHolds (g : Guard) (t : ℝ) : Prop :=
  ∀ a s, (a,s) ∈ g → if s then a.value t < 0 else a.value t ≤ 0

theorem guard_exact (g : Guard) (t z : ℝ) :
    z ∈ piece (guardAtoms g) t ↔ guardHolds g t := by
  have h (a : QAffine) (s : Bool) :
      (Atom.mk (a.atOne-a.atZero) 0 a.atZero s).Holds t z ↔
      if s then a.value t < 0 else a.value t ≤ 0 := by
    cases s <;> simp [Atom.Holds,QAffine.value] <;>
      constructor <;> intro h <;> nlinarith
  constructor
  · intro hg a s hm
    exact (h a s).mp (hg _ (List.mem_map.mpr ⟨(a,s),hm,rfl⟩))
  · intro hg a ha
    obtain ⟨⟨q,s⟩,hm,rfl⟩ := List.mem_map.mp ha
    exact (h q s).mpr (hg q s hm)

/-- A guarded open/closed affine band; contradictory/reversed bounds stay empty. -/
def band (g : Guard) (l u : QAffine) (ls us : Bool) : Description :=
  .cell (guardAtoms g ++ [lower l ls,upper u us])

theorem band_exact (g : Guard) (l u : QAffine) (ls us : Bool) (t z : ℝ) :
    z ∈ pieces (band g l u ls us).compile t ↔
      guardHolds g t ∧ (if ls then l.value t < z else l.value t ≤ z) ∧
        (if us then z < u.value t else z ≤ u.value t) := by
  rw [compile_exact]
  change z ∈ piece (guardAtoms g ++ [lower l ls,upper u us]) t ↔ _
  rw [piece_append]
  simp only [Set.mem_inter_iff,guard_exact]
  simp [piece,lower_exact,upper_exact]

/-- Each conjunction piece is order-convex in its output fiber, even if empty. -/
theorem piece_between (c : Piece) (t x y z : ℝ) (hx : x ∈ piece c t)
    (hy : y ∈ piece c t) (hxz : x ≤ z) (hzy : z ≤ y) : z ∈ piece c t := by
  intro a ha
  have hax := hx a ha
  have hay := hy a ha
  have hb : (a.output:ℝ)*z ≤ (a.output:ℝ)*y ∨
      (a.output:ℝ)*z ≤ (a.output:ℝ)*x := by
    by_cases hq : 0 ≤ (a.output:ℝ)
    · exact Or.inl (mul_le_mul_of_nonneg_left hzy hq)
    · exact Or.inr (mul_le_mul_of_nonpos_left hxz (le_of_not_ge hq))
  unfold Atom.Holds at *
  split_ifs at * <;> rcases hb with hb | hb <;> linarith

end GeneralizedIntervalArithmetic.FiniteGuardPieces
