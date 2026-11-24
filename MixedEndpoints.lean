import FiniteGuardPieces
import CoefficientWitnesses

/-! A concrete finite mixed-carrier model, not a source-prescribed convention
for open endpoints or persistence of choices in §2.14. -/
namespace GeneralizedIntervalArithmetic.MixedEndpoints
open FiniteGuardPieces

structure Band where
  lowerIntercept : ℤ
  lowerSlope : ℚ
  upperIntercept : ℚ
  upperSlope : ℤ
  lowerOpen : Bool
  upperOpen : Bool
  guards : Guard
  deriving DecidableEq, Repr

noncomputable def Band.lowerValue (b : Band) (t : ℝ) : ℝ :=
  b.lowerIntercept+b.lowerSlope*t
noncomputable def Band.upperValue (b : Band) (t : ℝ) : ℝ :=
  b.upperIntercept+b.upperSlope*t

def Band.denote (b : Band) (t : ℝ) : Set ℝ := {z |
  guardHolds b.guards t ∧
  (if b.lowerOpen then b.lowerValue t < z else b.lowerValue t ≤ z) ∧
  (if b.upperOpen then z < b.upperValue t else z ≤ b.upperValue t)}

def Band.lower (b : Band) : QAffine :=
  QAffine.ofCoefficients b.lowerIntercept b.lowerSlope
def Band.upper (b : Band) : QAffine :=
  QAffine.ofCoefficients b.upperIntercept b.upperSlope

def Band.encode (b : Band) : Description :=
  band b.guards b.lower b.upper b.lowerOpen b.upperOpen

theorem lower_value (b : Band) (t : ℝ) : b.lower.value t = b.lowerValue t := by
  simp [Band.lower,affine_ofCoefficients_value,Band.lowerValue]
theorem upper_value (b : Band) (t : ℝ) : b.upper.value t = b.upperValue t := by
  simp [Band.upper,affine_ofCoefficients_value,Band.upperValue]

/-- Exact finite conversion preserves strictness as well as endpoint values. -/
theorem encode_exact (b : Band) (t : ℝ) :
    pieces b.encode.compile t = b.denote t := by
  ext z
  simp [Band.encode,band_exact,lower_value,upper_value,Band.denote]

theorem rational_test_exact (b : Band) (t z : ℚ) :
    test b.encode.compile t z = true ↔ (z:ℝ) ∈ b.denote (t:ℝ) := by
  rw [test_exact,encode_exact]

/-- The heterogeneous endpoint values use the same coefficient pair at all
parameters. Reuse the existing code-to-real-witness correspondence. -/
theorem endpoint_witnesses (b : Band) (T : Set ℝ) :
    CoefficientWitnesses.realizes
      (CoefficientWitnesses.decodePairs (fun p : ℤ => (p:ℝ)) (fun q : ℚ => (q:ℝ))
        {(b.lowerIntercept,b.lowerSlope)}) T b.lowerValue ∧
    CoefficientWitnesses.realizes
      (CoefficientWitnesses.decodePairs (fun p : ℚ => (p:ℝ)) (fun q : ℤ => (q:ℝ))
        {(b.upperIntercept,b.upperSlope)}) T b.upperValue := by
  constructor
  · apply (CoefficientWitnesses.coded_exact _ _ _ _ _).mp
    exact ⟨(b.lowerIntercept,b.lowerSlope),Set.mem_singleton _,fun _ _ => rfl⟩
  · apply (CoefficientWitnesses.coded_exact _ _ _ _ _).mp
    exact ⟨(b.upperIntercept,b.upperSlope),Set.mem_singleton _,fun _ _ => rfl⟩

/-- Existing existential piece semantics, with the same parameter t. -/
theorem family_exact (C : Set Band) (t : ℝ) :
    IntervalSetDenotation.denote (fun d : Description => fun s => pieces d.compile s)
      (Band.encode '' C) t = IntervalSetDenotation.denote Band.denote C t :=
  IntervalSetDenotation.reencode Band.denote
    (fun d : Description => fun s => pieces d.compile s) Band.encode encode_exact C t

/-- One source band must witness every use on T. The target existential also
occurs OUTSIDE the universal quantifier; no fresh independent re-choice. -/
theorem joint_exact (C : Set Band) (T : Set ℝ) (f : ℝ → ℝ) :
    (∃ b ∈ C, ∀ t ∈ T, f t ∈ b.denote t) ↔
    (∃ d ∈ Band.encode '' C, ∀ t ∈ T, f t ∈ pieces d.compile t) := by
  constructor
  · rintro ⟨b,hb,hf⟩
    exact ⟨b.encode,⟨b,hb,rfl⟩,fun t ht => (encode_exact b t).symm ▸ hf t ht⟩
  · rintro ⟨_,⟨b,hb,rfl⟩,hf⟩
    exact ⟨b,hb,fun t ht => encode_exact b t ▸ hf t ht⟩

theorem empty_fiber (b : Band) (t : ℝ) :
    pieces b.encode.compile t = ∅ ↔ b.denote t = ∅ := by rw [encode_exact]

/-- Exact boundary criterion, without assuming the supplied endpoints are ordered. -/
theorem bounds_nonempty (l u : ℝ) (lo hi : Bool) :
    ({z : ℝ | (if lo then l<z else l≤z) ∧ (if hi then z<u else z≤u)}).Nonempty ↔
      l<u ∨ (l=u ∧ lo=false ∧ hi=false) := by
  cases lo <;> cases hi
  · change (Set.Icc l u).Nonempty ↔ _
    simp [Set.nonempty_Icc,le_iff_lt_or_eq]
  · change (Set.Ico l u).Nonempty ↔ _
    simp [Set.nonempty_Ico]
  · change (Set.Ioc l u).Nonempty ↔ _
    simp [Set.nonempty_Ioc]
  · change (Set.Ioo l u).Nonempty ↔ _
    simp [Set.nonempty_Ioo]

theorem fiber_nonempty (b : Band) (t : ℝ) :
    (pieces b.encode.compile t).Nonempty ↔ guardHolds b.guards t ∧
      (b.lowerValue t < b.upperValue t ∨
       (b.lowerValue t=b.upperValue t ∧ b.lowerOpen=false ∧ b.upperOpen=false)) := by
  rw [encode_exact]
  change (∃ z, guardHolds b.guards t ∧ _) ↔ _
  rw [← bounds_nonempty]
  constructor
  · rintro ⟨z,hg,hz⟩; exact ⟨hg,⟨z,hz⟩⟩
  · rintro ⟨hg,⟨z,hz⟩⟩; exact ⟨z,hg,hz⟩

end GeneralizedIntervalArithmetic.MixedEndpoints
