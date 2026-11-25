import AffinePoleSplit

/-! Affine translation in the existing finite half-space representation, including
unbounded fibers. All members are real; exceptional tags are separate. -/
namespace GeneralizedIntervalArithmetic.UnboundedPieceComposition
open FiniteGuardPieces AffinePoleSplit

/-- Substitute z - s(t) in an existing atom; retain its boundary flag. -/
def shiftAtom (s : QAffine) (a : Atom) : Atom :=
  ⟨a.parameter-a.output*(s.atOne-s.atZero),a.output,
    a.constant-a.output*s.atZero,a.strict⟩

def shift (s : QAffine) (cs : List Piece) : List Piece :=
  cs.map (fun c => c.map (shiftAtom s))

theorem shift_atom_exact (s : QAffine) (a : Atom) (t z : ℝ) :
    (shiftAtom s a).Holds t z ↔ a.Holds t (z-s.value t) := by
  have he : ((a.parameter-a.output*(s.atOne-s.atZero):ℚ):ℝ)*t+
      (a.output:ℝ)*z+((a.constant-a.output*s.atZero:ℚ):ℝ) =
      (a.parameter:ℝ)*t+(a.output:ℝ)*(z-s.value t)+(a.constant:ℝ) := by
    push_cast; unfold QAffine.value; ring
  simp only [shiftAtom,Atom.Holds,he]

theorem shift_exact (s : QAffine) (cs : List Piece) (t z : ℝ) :
    z ∈ pieces (shift s cs) t ↔ z-s.value t ∈ pieces cs t := by
  simp [shift,pieces,IntervalSetDenotation.denote,piece,shift_atom_exact]

theorem shift_image (s : QAffine) (cs : List Piece) (t : ℝ) :
    pieces (shift s cs) t = (fun z => z+s.value t) '' pieces cs t := by
  ext z
  rw [shift_exact]
  constructor
  · intro hz; exact ⟨z-s.value t,hz,by ring⟩
  · rintro ⟨v,hv,rfl⟩; simpa using hv

theorem shift_nonempty (s : QAffine) (cs : List Piece) (t : ℝ) :
    (pieces (shift s cs) t).Nonempty ↔ (pieces cs t).Nonempty := by
  rw [shift_image,Set.image_nonempty]

/-- No source output is created at a missing parameter. -/
theorem shift_empty (s : QAffine) (cs : List Piece) (t : ℝ) :
    pieces (shift s cs) t = ∅ ↔ pieces cs t = ∅ := by
  rw [←Set.not_nonempty_iff_eq_empty,←Set.not_nonempty_iff_eq_empty,shift_nonempty]

/-- The exact translation can be composed with a previously proved enclosure. -/
theorem shift_encloses (s : QAffine) (cs : List Piece) (R : ℝ → ℝ → Prop)
    (h : ∀ t v, R t v → v ∈ pieces cs t) {t z : ℝ}
    (hz : ∃ v, R t v ∧ z = v+s.value t) : z ∈ pieces (shift s cs) t := by
  rcases hz with ⟨v,hv,rfl⟩
  rw [shift_exact]
  simpa using h t v hv

/-- A syntactic guard is unchanged, not evaluated with a fresh parameter. -/
theorem shift_guard (s : QAffine) (g : Guard) :
    (guardAtoms g).map (shiftAtom s) = guardAtoms g := by
  simp [guardAtoms,List.map_map,shiftAtom]

def reciprocalCode (g : Guard) (d : QAffine) (l u : ℚ) : Description :=
  .union (.cell (guardAtoms (negative g d) ++ [upper ⟨1/l,1/l⟩ false]))
    (.cell (guardAtoms (positive g d) ++ [lower ⟨1/u,1/u⟩ false]))

theorem reciprocal_code_exact (g : Guard) (d : QAffine) (l u : ℚ) (t z : ℝ) :
    z ∈ pieces (reciprocalCode g d l u).compile t ↔
      (guardHolds g t ∧ d.value t < 0 ∧ z ≤ 1/(l:ℝ)) ∨
      (guardHolds g t ∧ 0 < d.value t ∧ 1/(u:ℝ) ≤ z) := by
  rw [compile_exact]
  change (z ∈ piece (guardAtoms (negative g d) ++ _) t ∨
    z ∈ piece (guardAtoms (positive g d) ++ _) t) ↔ _
  rw [piece_append,piece_append]
  simp only [Set.mem_inter_iff,guard_exact,negative_exact,positive_exact]
  have hc (q : ℚ) : (⟨q,q⟩ : QAffine).value t = (q:ℝ) := by
    unfold QAffine.value; ring
  simp [piece,upper_exact,lower_exact,hc,and_assoc]

/-- The output rays are nonempty exactly on the original partial domain.
Their numerical soundness is a separate theorem with bound premises. -/
theorem reciprocal_domain (g : Guard) (d : QAffine) (l u : ℚ) (t : ℝ) :
    (pieces (reciprocalCode g d l u).compile t).Nonempty ↔
      ∃ v, AffinePoleSplit.Values g d t v := by
  constructor
  · rintro ⟨z,hz⟩
    rcases (reciprocal_code_exact g d l u t z).1 hz with h | h
    · exact ⟨1/d.value t,h.1,ne_of_lt h.2.1,rfl⟩
    · exact ⟨1/d.value t,h.1,ne_of_gt h.2.1,rfl⟩
  · rintro ⟨v,hg,hn,_⟩
    rcases lt_or_gt_of_ne hn with h | h
    · exact ⟨1/(l:ℝ),(reciprocal_code_exact g d l u t _).2 (Or.inl ⟨hg,h,le_rfl⟩)⟩
    · exact ⟨1/(u:ℝ),(reciprocal_code_exact g d l u t _).2 (Or.inr ⟨hg,h,le_rfl⟩)⟩

theorem reciprocal_encloses {g : Guard} {d : QAffine} {l u : ℚ}
    (hb : ∀ t, guardHolds g t → (l:ℝ) ≤ d.value t ∧ d.value t ≤ (u:ℝ))
    {t z : ℝ} (hz : AffinePoleSplit.Values g d t z) :
    z ∈ pieces (reciprocalCode g d l u).compile t := by
  obtain ⟨hg,hn,rfl⟩ := hz
  rw [reciprocal_code_exact]
  rcases lt_or_gt_of_ne hn with h | h
  · refine Or.inl ⟨hg,h,?_⟩
    have hh := SplitQuotient.negative_bound (a:=(1:ℝ)) (x:=1) (c:=-(l:ℝ))
      (by norm_num) le_rfl (by simpa using (hb t hg).1) h
    simpa using hh
  · exact Or.inr ⟨hg,h,SplitQuotient.positive_bound (by norm_num) le_rfl (hb t hg).2 h⟩

/-- Generated domain survives the second, total operation. -/
theorem composed_domain (s : QAffine) (g : Guard) (d : QAffine) (l u : ℚ) (t : ℝ) :
    (pieces (shift s (reciprocalCode g d l u).compile) t).Nonempty ↔
      ∃ z v, AffinePoleSplit.Values g d t v ∧ z = v+s.value t := by
  rw [shift_nonempty,reciprocal_domain]
  constructor
  · rintro ⟨v,hv⟩; exact ⟨v+s.value t,v,hv,rfl⟩
  · rintro ⟨z,v,hv,_⟩; exact ⟨v,hv⟩

theorem composed_encloses {g : Guard} {d s : QAffine} {l u : ℚ}
    (hb : ∀ t, guardHolds g t → (l:ℝ) ≤ d.value t ∧ d.value t ≤ (u:ℝ))
    {t z : ℝ} (hz : ∃ v, AffinePoleSplit.Values g d t v ∧ z = v+s.value t) :
    z ∈ pieces (shift s (reciprocalCode g d l u).compile) t :=
  shift_encloses s _ _ (fun _ _ hv => reciprocal_encloses hb hv) hz

/-- Connect composition to the existing AST without replacing its semantics. -/
theorem composed_expression (g : Guard) (d s : QAffine) (t z : ℝ) :
    (∃ v, AffinePoleSplit.Values g d t v ∧ z = v+s.value t) ↔
      guardHolds g t ∧ Value (d.value t) (s.value t)
        (.add (.div (.const 1) .x) .y) z := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    have he := (AffinePoleSplit.expression_exact g d t v (s.value t)).1 hv
    exact ⟨he.1,Value.add he.2 Value.y⟩
  · rintro ⟨hg,hv⟩
    cases hv with
    | add ha hb =>
      cases hb
      exact ⟨_,(AffinePoleSplit.expression_exact g d t _ (s.value t)).2 ⟨hg,ha⟩,rfl⟩

/-- Encoding real pieces as finite tags never inserts genuine infinities or λ,
even if a subsequent hull has infinite bounds. -/
theorem finite_tags_only (S : Set ℝ) :
    let T := ExceptionalComparisons.Value.finite '' S
    let H := TaggedConversion.lift ExtendedImageHull.hull T
    ExceptionalComparisons.Value.posInf ∉ H ∧
    ExceptionalComparisons.Value.negInf ∉ H ∧
    ExceptionalComparisons.Value.undefined ∉ H := by
  change ExceptionalComparisons.Value.posInf ∉ ExceptionalComparisons.Value.finite '' S ∧
    ExceptionalComparisons.Value.negInf ∉ ExceptionalComparisons.Value.finite '' S ∧
    ExceptionalComparisons.Value.undefined ∉ ExceptionalComparisons.Value.finite '' S
  simp

end GeneralizedIntervalArithmetic.UnboundedPieceComposition
