import MixedEndpoints
import DomainConstraints

/-! Constructive finite-band value/domain conversion. Syntax and exact rational
checks reuse FiniteGuardPieces; no real quantifier elimination is assumed. -/
namespace GeneralizedIntervalArithmetic.PieceDomainConversion
open FiniteGuardPieces MixedEndpoints

/-- A strict feasibility constraint is required if either endpoint is open. -/
def activeGuard (b : Band) : Guard :=
  b.guards ++ [(b.lower.sub b.upper, b.lowerOpen || b.upperOpen)]

theorem active_iff (b : Band) (t : ℝ) :
    guardHolds (activeGuard b) t ↔ (b.denote t).Nonempty := by
  have hg : guardHolds (activeGuard b) t ↔ guardHolds b.guards t ∧
      (if b.lowerOpen || b.upperOpen then b.lowerValue t < b.upperValue t
       else b.lowerValue t ≤ b.upperValue t) := by
    simp only [activeGuard,guardHolds,List.mem_append,List.mem_singleton,or_imp,forall_and]
    constructor
    · intro h
      refine ⟨h.1,?_⟩
      have hh := h.2 (b.lower.sub b.upper) (b.lowerOpen || b.upperOpen) rfl
      rw [affine_sub_value,lower_value,upper_value] at hh
      split_ifs at hh ⊢ <;> linarith
    · rintro ⟨h,hb⟩
      refine ⟨h,?_⟩
      intro a s he
      cases he
      simp only [affine_sub_value,lower_value,upper_value]
      split_ifs at hb ⊢ <;> linarith
  rw [hg,← encode_exact, fiber_nonempty]
  cases b.lowerOpen <;> cases b.upperOpen <;> simp [le_iff_lt_or_eq]

/-- Separate numerical bounds and an explicit parameter-only description. -/
def valueCode (b : Band) : Description := band [] b.lower b.upper false false
def domainCode (b : Band) : Description := .cell (guardAtoms (activeGuard b))
def converted (b : Band) : Description := .inter (valueCode b) (domainCode b)

theorem valueCode_exact (b : Band) (t z : ℝ) :
    z ∈ (valueCode b).denote t ↔ b.lowerValue t ≤ z ∧ z ≤ b.upperValue t := by
  rw [← compile_exact]
  simp [valueCode,band_exact,guardHolds,lower_value,upper_value]

theorem domainCode_exact (b : Band) (t z : ℝ) :
    z ∈ (domainCode b).denote t ↔ (b.denote t).Nonempty := by
  exact (guard_exact (activeGuard b) t z).trans (active_iff b t)

theorem converted_exact (b : Band) (t z : ℝ) :
    z ∈ (converted b).denote t ↔
      (b.lowerValue t ≤ z ∧ z ≤ b.upperValue t) ∧ (b.denote t).Nonempty := by
  simp only [converted,Description.denote,Set.mem_inter_iff,valueCode_exact,domainCode_exact]

theorem converted_encloses (b : Band) (t : ℝ) : b.denote t ⊆ (converted b).denote t := by
  intro z hz
  apply (converted_exact b t z).2
  refine ⟨⟨?_,?_⟩,⟨z,hz⟩⟩
  · have h := hz.2.1
    split_ifs at h <;> linarith
  · have h := hz.2.2
    split_ifs at h <;> linarith

theorem converted_nonempty (b : Band) (t : ℝ) :
    ((converted b).denote t).Nonempty ↔ (b.denote t).Nonempty := by
  constructor
  · rintro ⟨z,hz⟩
    exact ((converted_exact b t z).1 hz).2
  · rintro ⟨z,hz⟩
    exact ⟨z,converted_encloses b t hz⟩

def active? (b : Band) (t : ℚ) : Bool := test (domainCode b).compile t 0

theorem active_test_exact (b : Band) (t : ℚ) :
    active? b t = true ↔ (b.denote (t:ℝ)).Nonempty := by
  rw [active?,compiled_test_exact,domainCode_exact]

def possible? (bs : List Band) (t : ℚ) : Bool := bs.any (fun b => active? b t)
def definite? (bs : List Band) (t : ℚ) : Bool := !bs.isEmpty && bs.all (fun b => active? b t)

theorem possible_test_exact (bs : List Band) (t : ℚ) :
    possible? bs t = true ↔ ∃ b ∈ bs, (b.denote (t:ℝ)).Nonempty := by
  simp [possible?,active_test_exact]

theorem definite_test_exact (bs : List Band) (t : ℚ) :
    definite? bs t = true ↔ bs ≠ [] ∧ ∀ b ∈ bs, (b.denote (t:ℝ)).Nonempty := by
  simp [definite?,active_test_exact]

/-- Original choice remains a witness; a union does not assert every choice works. -/
def source (bs : List Band) (t : ℝ) : Set ℝ :=
  {z | ∃ b ∈ bs, z ∈ b.denote t}

def compileValues (bs : List Band) : List Piece := bs.flatMap (fun b => (converted b).compile)
def compileDomain (bs : List Band) : List Piece := bs.flatMap (fun b => (domainCode b).compile)

theorem flatMap_exact (bs : List Band) (f : Band → Description) (t z : ℝ) :
    z ∈ pieces (bs.flatMap (fun b => (f b).compile)) t ↔
      ∃ b ∈ bs, z ∈ (f b).denote t := by
  simp only [pieces,IntervalSetDenotation.denote,Set.mem_setOf_eq,List.mem_flatMap]
  constructor
  · rintro ⟨c,⟨b,hb,hc⟩,hz⟩
    exact ⟨b,hb,(compile_exact (f b) t) ▸ (show z ∈ pieces (f b).compile t from ⟨c,hc,hz⟩)⟩
  · rintro ⟨b,hb,hz⟩
    rw [← compile_exact] at hz
    obtain ⟨c,hc,hz⟩ := hz
    exact ⟨c,⟨b,hb,hc⟩,hz⟩

theorem values_enclose (bs : List Band) (t : ℝ) : source bs t ⊆ pieces (compileValues bs) t := by
  rintro z ⟨b,hb,hz⟩
  exact (flatMap_exact bs converted t z).2 ⟨b,hb,converted_encloses b t hz⟩

theorem domain_exact (bs : List Band) (t z : ℝ) :
    z ∈ pieces (compileDomain bs) t ↔ (source bs t).Nonempty := by
  rw [compileDomain,flatMap_exact]
  simp only [domainCode_exact,source,Set.Nonempty,Set.mem_setOf_eq]
  aesop

theorem values_nonempty (bs : List Band) (t : ℝ) :
    (pieces (compileValues bs) t).Nonempty ↔ (source bs t).Nonempty := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨b,hb,hz⟩ := (flatMap_exact bs converted t z).1 hz
    obtain ⟨x,hx⟩ := ((converted_exact b t z).1 hz).2
    exact ⟨x,b,hb,hx⟩
  · rintro ⟨z,hz⟩
    exact ⟨z,values_enclose bs t hz⟩

/-- Full per-choice domain envelope, not just existence in the union. -/
def sourceDomain (bs : List Band) : DomainBounds ℝ :=
  exactInputDomain (fun _ b => b ∈ bs) (fun t b z => z ∈ b.denote t)
def targetDomain (bs : List Band) : DomainBounds ℝ :=
  exactInputDomain (fun _ b => b ∈ bs) (fun t b z => z ∈ (converted b).denote t)

theorem classification_exact (bs : List Band) (t : ℝ) :
    (sourceDomain bs).definite t = (targetDomain bs).definite t ∧
    (sourceDomain bs).possible t = (targetDomain bs).possible t := by
  simp only [sourceDomain,targetDomain,exactInputDomain]
  have h (b : Band) : (∃ z, z ∈ (converted b).denote t) ↔ ∃ z, z ∈ b.denote t :=
    converted_nonempty b t
  simp only [exists_and_left,h,eq_self,and_self]
theorem executable_domain_exact (bs : List Band) (t : ℚ) :
    (definite? bs t = true ↔ (sourceDomain bs).definite (t:ℝ)) ∧
    (possible? bs t = true ↔ (sourceDomain bs).possible (t:ℝ)) := by
  rw [definite_test_exact,possible_test_exact]
  simp only [sourceDomain,exactInputDomain,Set.Nonempty,exists_and_left]
  have hn : (∃ b, b ∈ bs) ↔ bs ≠ [] :=
    ⟨fun ⟨_,h⟩ => List.ne_nil_of_mem h, List.exists_mem_of_ne_nil bs⟩
  simp only [hn,iff_self,and_self]

def classify (bs : List Band) (t : ℚ) : StrictComparison.Truth :=
  if definite? bs t then .trueOnly else if possible? bs t then .both else .falseOnly

theorem classify_exact (bs : List Band) (t : ℚ) :
    classify bs t = DomainConstraints.description (sourceDomain bs) (t:ℝ) := by
  classical
  have hd := (executable_domain_exact bs t).1
  have hp := (executable_domain_exact bs t).2
  simp only [classify,DomainConstraints.description,hd,hp]

/-- Both value inclusion and each original choice's domain obligations. -/
theorem coupled_sound (bs : List Band) (t : ℝ) (b : Band) (hb : b ∈ bs) :
    (∀ z ∈ b.denote t, z ∈ pieces (compileValues bs) t) ∧
    (targetDomain bs).Compatible t ((b.denote t).Nonempty) := by
  refine ⟨fun z hz => values_enclose bs t ⟨b,hb,hz⟩,?_,?_⟩
  · intro h
    exact (converted_nonempty b t).1 (h.2 b hb)
  · rintro ⟨z,hz⟩
    exact ⟨b,z,hb,converted_encloses b t hz⟩

end GeneralizedIntervalArithmetic.PieceDomainConversion
