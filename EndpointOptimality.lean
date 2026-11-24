import Binary64Format
import FiniteAffineDemotion

namespace GeneralizedIntervalArithmetic.EndpointOptimality
open DiscreteDemotion

/-- Greatest repaired-format lower bound, including its soundness obligation. -/
def LowerOptimal (x : ℝ) (l : ℚ) : Prop :=
  (l:ℝ) ≤ x ∧ ∀ q : ℚ, FormatDigits.Repaired Binary64Format.format q → (q:ℝ) ≤ x → q ≤ l

def UpperOptimal (x : ℝ) (u : ℚ) : Prop :=
  x ≤ (u:ℝ) ∧ ∀ q : ℚ, FormatDigits.Repaired Binary64Format.format q → x ≤ (q:ℝ) → u ≤ q

theorem decoded_down_iff {w : Binary64.Word} {l : ℚ}
    (hl : Binary64.decode w = some l) (x : ℝ) :
    down binaryValues (x:EReal) = ((l:ℝ):EReal) ↔ LowerOptimal x l := by
  constructor
  · intro h
    refine ⟨EReal.coe_le_coe_iff.mp (h ▸ (down_spec _ _).2),?_⟩
    intro q hq hqx
    have hm := (Binary64Format.repaired_iff_binaryValues q).mp hq
    have he := (mem_endpoints binaryValues ((q:ℝ):EReal)).mpr (Or.inr (Or.inr ⟨q,hm,rfl⟩))
    have hh := down_greatest he (EReal.coe_le_coe_iff.mpr hqx)
    rw [h] at hh
    exact_mod_cast hh
  · rintro ⟨hlx,hbest⟩
    apply down_eq (decoded_representable hl) (EReal.coe_le_coe_iff.mpr hlx)
    intro v hv hvx
    rcases (mem_endpoints _ _).mp hv with rfl | rfl | ⟨q,hq,rfl⟩
    · exact bot_le
    · simp at hvx
    · have hqx : (q:ℝ) ≤ x := EReal.coe_le_coe_iff.mp hvx
      exact_mod_cast hbest q ((Binary64Format.repaired_iff_binaryValues q).mpr hq) hqx

theorem decoded_up_iff {w : Binary64.Word} {u : ℚ}
    (hu : Binary64.decode w = some u) (x : ℝ) :
    up binaryValues (x:EReal) = ((u:ℝ):EReal) ↔ UpperOptimal x u := by
  constructor
  · intro h
    refine ⟨EReal.coe_le_coe_iff.mp (h ▸ (up_spec _ _).2),?_⟩
    intro q hq hxq
    have hm := (Binary64Format.repaired_iff_binaryValues q).mp hq
    have he := (mem_endpoints binaryValues ((q:ℝ):EReal)).mpr (Or.inr (Or.inr ⟨q,hm,rfl⟩))
    have hh := up_least he (EReal.coe_le_coe_iff.mpr hxq)
    rw [h] at hh
    exact_mod_cast hh
  · rintro ⟨hxu,hbest⟩
    apply up_eq (decoded_representable hu) (EReal.coe_le_coe_iff.mpr hxu)
    intro v hv hxv
    rcases (mem_endpoints _ _).mp hv with rfl | rfl | ⟨q,hq,rfl⟩
    · simp at hxv
    · exact le_top
    · have hxq : x ≤ (q:ℝ) := EReal.coe_le_coe_iff.mp hxv
      exact_mod_cast hbest q ((Binary64Format.repaired_iff_binaryValues q).mpr hq) hxq

theorem contains_iff {O : HardwareAddition.Bounds Binary64.Word} {l u : ℚ}
    (hl : Binary64.decode O.lo = some l) (hu : Binary64.decode O.hi = some u) (x : ℝ) :
    HardwareAddition.Contains Binary64.real O x ↔ x ∈ Set.Icc (l:ℝ) (u:ℝ) := by
  simp [HardwareAddition.Contains,Binary64.real,hl,hu]

/-- On an actual nonempty image, equality of the interval sets is equivalent
 to endpoint optimality. Finite successful certificates themselves give bounds. -/
theorem certificate_exact_iff {S : Set ℝ} (hne : S.Nonempty)
    {O : HardwareAddition.Bounds Binary64.Word} {l u : ℚ}
    (hl : Binary64.decode O.lo = some l) (hu : Binary64.decode O.hi = some u)
    (hc : ∀ x ∈ S, HardwareAddition.Contains Binary64.real O x) :
    hull binaryValues S = {x | HardwareAddition.Contains Binary64.real O x} ↔
      LowerOptimal (sInf S) l ∧ UpperOptimal (sSup S) u := by
  have hs : S ⊆ Set.Icc (l:ℝ) (u:ℝ) := fun x hx => (contains_iff hl hu x).mp (hc x hx)
  have hb : BddBelow S := ⟨l,fun x hx => (hs hx).1⟩
  have ha : BddAbove S := ⟨u,fun x hx => (hs hx).2⟩
  have hli : (l:ℝ) ≤ sInf S := le_csInf hne (fun x hx => (hs hx).1)
  have hiu : sSup S ≤ (u:ℝ) := csSup_le hne (fun x hx => (hs hx).2)
  obtain ⟨v,hv⟩ := hne
  have hlu : (l:ℝ) ≤ u := (hs hv).1.trans (hs hv).2
  have hcset : {x | HardwareAddition.Contains Binary64.real O x} = Set.Icc (l:ℝ) (u:ℝ) :=
    Set.ext (contains_iff hl hu)
  rw [hcset,finite_formula binaryValues ⟨v,hv⟩ hb ha]
  rw [← decoded_down_iff hl,← decoded_up_iff hu]
  constructor
  · intro heq
    have hml : (l:ℝ) ∈ ExtendedImageHull.interval
        (down binaryValues (sInf S:ℝ)) (up binaryValues (sSup S:ℝ)) := by rw [heq]; exact ⟨le_rfl,hlu⟩
    have hmu : (u:ℝ) ∈ ExtendedImageHull.interval
        (down binaryValues (sInf S:ℝ)) (up binaryValues (sSup S:ℝ)) := by rw [heq]; exact ⟨hlu,le_rfl⟩
    exact ⟨le_antisymm hml.1 (down_greatest (decoded_representable hl) (EReal.coe_le_coe_iff.mpr hli)),
      le_antisymm (up_least (decoded_representable hu) (EReal.coe_le_coe_iff.mpr hiu)) hmu.2⟩
  · rintro ⟨hd,hu'⟩
    rw [hd,hu']
    ext x
    simp [ExtendedImageHull.interval]

/-- Closed ideal intervals provide their actual extrema, not assumed Cartesian inputs. -/
theorem interval_exact_iff {a b : ℝ} (hab : a ≤ b)
    {O : HardwareAddition.Bounds Binary64.Word} {l u : ℚ}
    (hl : Binary64.decode O.lo = some l) (hu : Binary64.decode O.hi = some u)
    (hla : (l:ℝ) ≤ a) (hbu : b ≤ (u:ℝ)) :
    hull binaryValues (Set.Icc a b) = {x | HardwareAddition.Contains Binary64.real O x} ↔
      LowerOptimal a l ∧ UpperOptimal b u := by
  have hc : ∀ x ∈ Set.Icc a b, HardwareAddition.Contains Binary64.real O x := by
    intro x hx
    exact (contains_iff hl hu x).mpr ⟨hla.trans hx.1,hx.2.trans hbu⟩
  simpa [csInf_Icc hab,csSup_Icc hab] using
    (certificate_exact_iff (Set.nonempty_Icc.mpr hab) hl hu hc)

/-- Specialize to the existing executable certificate's zero endpoint. The
 certificate supplies soundness; coincidence still requires optimality. -/
theorem certified_zero_exact_iff {I : LinearInterval} {H O : HardwareAffine.Form Binary64.Word}
    (h : FiniteAffineDemotion.certify I H = some O) : ∃ l u : ℚ,
    Binary64.decode O.atZero.lo = some l ∧ Binary64.decode O.atZero.hi = some u ∧
    (hull binaryValues (Set.Icc (I.lower.atZero:ℝ) (I.upper.atZero:ℝ)) =
      {x | HardwareAddition.Contains Binary64.real O.atZero x} ↔
      LowerOptimal (I.lower.atZero:ℝ) l ∧ UpperOptimal (I.upper.atZero:ℝ) u) := by
  obtain ⟨rfl,l,u,l1,u1,hl,hu,_,_,hla,hbu,_,_⟩ := FiniteAffineDemotion.certify_spec h
  exact ⟨l,u,hl,hu,interval_exact_iff (by exact_mod_cast I.orderedZero) hl hu
    (by exact_mod_cast hla) (by exact_mod_cast hbu)⟩

/-- The other stored endpoint has the same independent optimality obligation. -/
theorem certified_one_exact_iff {I : LinearInterval} {H O : HardwareAffine.Form Binary64.Word}
    (h : FiniteAffineDemotion.certify I H = some O) : ∃ l u : ℚ,
    Binary64.decode O.atOne.lo = some l ∧ Binary64.decode O.atOne.hi = some u ∧
    (hull binaryValues (Set.Icc (I.lower.atOne:ℝ) (I.upper.atOne:ℝ)) =
      {x | HardwareAddition.Contains Binary64.real O.atOne x} ↔
      LowerOptimal (I.lower.atOne:ℝ) l ∧ UpperOptimal (I.upper.atOne:ℝ) u) := by
  obtain ⟨rfl,l0,u0,l,u,_,_,hl,hu,_,_,hla,hbu⟩ := FiniteAffineDemotion.certify_spec h
  exact ⟨l,u,hl,hu,interval_exact_iff (by exact_mod_cast I.orderedOne) hl hu
    (by exact_mod_cast hla) (by exact_mod_cast hbu)⟩

/-- Empty fibers stay empty; finite certified endpoints are only needed on
 inhabited fibers. The same parameter a is retained throughout. -/
theorem family_exact {α : Type*} (A : Set α) (S : α → Set ℝ)
    (O : α → HardwareAddition.Bounds Binary64.Word)
    (hc : ∀ a ∈ A, (S a).Nonempty → ∃ l u : ℚ,
      Binary64.decode (O a).lo = some l ∧ Binary64.decode (O a).hi = some u ∧
      (∀ z ∈ S a, HardwareAddition.Contains Binary64.real (O a) z) ∧
      LowerOptimal (sInf (S a)) l ∧ UpperOptimal (sSup (S a)) u) :
    ∀ a z, (a ∈ A ∧ z ∈ hull binaryValues (S a)) ↔
      a ∈ A ∧ (S a).Nonempty ∧ HardwareAddition.Contains Binary64.real (O a) z := by
  intro a z
  by_cases ha : a ∈ A
  · by_cases hn : (S a).Nonempty
    · obtain ⟨l,u,hl,hu,hs,ho⟩ := hc a ha hn
      have heq := (certificate_exact_iff hn hl hu hs).mpr ho
      simp [ha,hn,heq]
    · have he : S a = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      simp [ha,hn,he,empty]
  · simp [ha]

end GeneralizedIntervalArithmetic.EndpointOptimality
