import ExtendedImageHull
import Binary64
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Option

namespace GeneralizedIntervalArithmetic.DiscreteDemotion

/-- A finite rational value family, with infinities added as ORDERED BOUNDS.
Neither undefined values nor IEEE exceptional arithmetic are modeled here. -/
noncomputable def endpoints (D : Finset ℚ) : Finset EReal :=
  insert ⊥ (insert ⊤ (D.image (fun q : ℚ => ((q:ℝ):EReal))))

theorem mem_endpoints (D : Finset ℚ) (x : EReal) :
    x ∈ endpoints D ↔ x = ⊥ ∨ x = ⊤ ∨ ∃ q ∈ D, x = ((q:ℝ):EReal) := by
  classical
  simp [endpoints,eq_comm]

noncomputable def down (D : Finset ℚ) (x : EReal) : EReal := by
  classical
  exact ((endpoints D).filter (· ≤ x)).max' ⟨⊥,by simp [endpoints]⟩
noncomputable def up (D : Finset ℚ) (x : EReal) : EReal := by
  classical
  exact ((endpoints D).filter (x ≤ ·)).min' ⟨⊤,by simp [endpoints]⟩

theorem down_spec (D : Finset ℚ) (x : EReal) :
    down D x ∈ endpoints D ∧ down D x ≤ x := by
  classical
  exact Finset.mem_filter.mp (Finset.max'_mem _ _)
theorem up_spec (D : Finset ℚ) (x : EReal) :
    up D x ∈ endpoints D ∧ x ≤ up D x := by
  classical
  exact Finset.mem_filter.mp (Finset.min'_mem _ _)

theorem down_greatest {D : Finset ℚ} {a x : EReal}
    (ha : a ∈ endpoints D) (h : a ≤ x) : a ≤ down D x := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨ha,h⟩)
theorem up_least {D : Finset ℚ} {a x : EReal}
    (ha : a ∈ endpoints D) (h : x ≤ a) : up D x ≤ a := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨ha,h⟩)

theorem fixed {D : Finset ℚ} {x : EReal} (h : x ∈ endpoints D) :
    down D x = x ∧ up D x = x :=
  ⟨le_antisymm (down_spec D x).2 (down_greatest h le_rfl),
   le_antisymm (up_least h le_rfl) (up_spec D x).2⟩

theorem monotone_down (D : Finset ℚ) : Monotone (down D) :=
  fun _ _ h => down_greatest (down_spec _ _).1 ((down_spec _ _).2.trans h)
theorem monotone_up (D : Finset ℚ) : Monotone (up D) :=
  fun _ _ h => up_least (up_spec _ _).1 (h.trans (up_spec _ _).2)

theorem infinity_fixed (D : Finset ℚ) :
    down D ⊥ = ⊥ ∧ up D ⊥ = ⊥ ∧ down D ⊤ = ⊤ ∧ up D ⊤ = ⊤ := by
  have hb := fixed (D:=D) (x:=⊥) (by simp [endpoints])
  have ht := fixed (D:=D) (x:=⊤) (by simp [endpoints])
  exact ⟨hb.1,hb.2,ht.1,ht.2⟩

noncomputable def hull (D : Finset ℚ) (S : Set ℝ) : Set ℝ :=
  ExtendedImageHull.interval (down D (ExtendedImageHull.lower S))
    (up D (ExtendedImageHull.upper S))

theorem sound (D : Finset ℚ) (S : Set ℝ) : S ⊆ hull D S := by
  intro x hx
  have h := ExtendedImageHull.sound S hx
  exact ⟨(down_spec _ _).2.trans h.1,h.2.trans (up_spec _ _).2⟩

theorem least {D : Finset ℚ} {S : Set ℝ} {l u : EReal}
    (hl : l ∈ endpoints D) (hu : u ∈ endpoints D)
    (he : S ⊆ ExtendedImageHull.interval l u) :
    hull D S ⊆ ExtendedImageHull.interval l u := by
  have hb := ExtendedImageHull.endpoint_least he
  intro x hx
  exact ⟨(down_greatest hl hb.1).trans hx.1,hx.2.trans (up_least hu hb.2)⟩

theorem hull_mono (D : Finset ℚ) {S T : Set ℝ} (h : S ⊆ T) : hull D S ⊆ hull D T :=
  least (down_spec _ _).1 (up_spec _ _).1 (h.trans (sound D T))

theorem hull_idempotent (D : Finset ℚ) (S : Set ℝ) : hull D (hull D S) = hull D S :=
  Set.Subset.antisymm (least (down_spec _ _).1 (up_spec _ _).1 (Set.Subset.refl _)) (sound _ _)

theorem empty (D : Finset ℚ) : hull D ∅ = ∅ := by
  unfold hull
  rw [ExtendedImageHull.empty_bounds.1,ExtendedImageHull.empty_bounds.2,
    (infinity_fixed D).2.2.1,(infinity_fixed D).2.1]
  ext x
  simp [ExtendedImageHull.interval]

theorem nonempty_iff (D : Finset ℚ) (S : Set ℝ) : (hull D S).Nonempty ↔ S.Nonempty := by
  constructor
  · intro h
    by_contra hn
    have hs : S=∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [hs,empty] at h
  · rintro ⟨x,hx⟩
    exact ⟨x,sound D S hx⟩

theorem unbounded_lower (D : Finset ℚ) {S : Set ℝ} (h : ¬ BddBelow S) :
    down D (ExtendedImageHull.lower S) = ⊥ := by
  rw [ExtendedImageHull.lower_unbounded h,(infinity_fixed D).1]
theorem unbounded_upper (D : Finset ℚ) {S : Set ℝ} (h : ¬ BddAbove S) :
    up D (ExtendedImageHull.upper S) = ⊤ := by
  rw [ExtendedImageHull.upper_unbounded h,(infinity_fixed D).2.2.2]

theorem relation_sound (D : Finset ℚ) {α : Type*} (A : Set α) (R : α → ℝ → Prop)
    {a : α} {z : ℝ} (ha : a ∈ A) (hz : R a z) :
    z ∈ hull D {v | ∃ w ∈ A, R w v} := sound _ _ ⟨a,ha,hz⟩

/-- Exact independent addition feeds the same demotion, not a separate arithmetic. -/
theorem add_enclosed (D : Finset ℚ) (I J : QInterval) {z : ℝ}
    (hz : (I.add J).Contains z) : z ∈ hull D (ExactImageHull.sums I J) := by
  have hlo := sound D _ (ExactImageHull.sums_endpoints I J).1
  have hhi := sound D _ (ExactImageHull.sums_endpoints I J).2
  exact ⟨hlo.1.trans (EReal.coe_le_coe_iff.mpr hz.1),
    (EReal.coe_le_coe_iff.mpr hz.2).trans hhi.2⟩

/-- Extremality characterizes the numerical result uniquely. -/
theorem down_eq {D : Finset ℚ} {a x : EReal} (ha : a ∈ endpoints D) (hax : a ≤ x)
    (hmax : ∀ v ∈ endpoints D, v ≤ x → v ≤ a) : down D x = a :=
  le_antisymm (hmax _ (down_spec _ _).1 (down_spec _ _).2) (down_greatest ha hax)
theorem up_eq {D : Finset ℚ} {a x : EReal} (ha : a ∈ endpoints D) (hxa : x ≤ a)
    (hmin : ∀ v ∈ endpoints D, x ≤ v → a ≤ v) : up D x = a :=
  le_antisymm (up_least ha hxa) (hmin _ (up_spec _ _).1 (up_spec _ _).2)

theorem fixed_iff (D : Finset ℚ) (x : EReal) :
    down D x = x ↔ x ∈ endpoints D := by
  constructor
  · intro h; simpa [h] using (down_spec D x).1
  · intro h; exact (fixed h).1

theorem finite_formula (D : Finset ℚ) {S : Set ℝ}
    (hne : S.Nonempty) (hl : BddBelow S) (hu : BddAbove S) :
    hull D S = ExtendedImageHull.interval (down D (sInf S : ℝ)) (up D (sSup S : ℝ)) := by
  unfold hull
  rw [ExtendedImageHull.lower_finite hne hl,ExtendedImageHull.upper_finite hne hu]

theorem endpoints_mono {D E : Finset ℚ} (h : D ⊆ E) : endpoints D ⊆ endpoints E := by
  intro x hx
  rw [mem_endpoints] at hx ⊢
  rcases hx with hbot | htop | ⟨q,hq,rfl⟩
  · exact Or.inl hbot
  · exact Or.inr (Or.inl htop)
  · exact Or.inr (Or.inr ⟨q,h hq,rfl⟩)

/-- More representable values cannot worsen the least outward enclosure. -/
theorem family_refinement {D E : Finset ℚ} (h : D ⊆ E) (S : Set ℝ) :
    hull E S ⊆ hull D S :=
  least (endpoints_mono h (down_spec _ _).1)
    (endpoints_mono h (up_spec _ _).1) (sound _ _)

/-- Pure directed conversion through a richer family agrees with direct conversion.
This says nothing about rounded intermediate arithmetic or nearest rounding. -/
theorem down_trans {D E : Finset ℚ} (h : D ⊆ E) (x : EReal) :
    down D (down E x) = down D x := by
  apply le_antisymm ((monotone_down D) (down_spec E x).2)
  exact down_greatest (down_spec _ _).1
    (down_greatest (endpoints_mono h (down_spec _ _).1) (down_spec _ _).2)

theorem up_trans {D E : Finset ℚ} (h : D ⊆ E) (x : EReal) :
    up D (up E x) = up D x := by
  apply le_antisymm _ ((monotone_up D) (up_spec E x).2)
  exact up_least (up_spec _ _).1
    (up_least (endpoints_mono h (up_spec _ _).1) (up_spec _ _).2)

/-- A mathematical finite set. Never enumerate 2^64 words in a runtime path. -/
@[irreducible] noncomputable def binaryValues : Finset ℚ :=
  (Finset.range (2^64)).biUnion (fun w => (Binary64.decode w).toFinset)

theorem mem_binaryValues (q : ℚ) : q ∈ binaryValues ↔
    ∃ w : Binary64.Word, w < 2^64 ∧ Binary64.decode w = some q := by
  simp [binaryValues,Option.mem_def,eq_comm]

theorem decoded_representable {w : Binary64.Word} {q : ℚ}
    (h : Binary64.decode w = some q) : ((q:ℝ):EReal) ∈ endpoints binaryValues := by
  apply (mem_endpoints _ _).mpr
  refine Or.inr (Or.inr ⟨q,(mem_binaryValues q).mpr ⟨w,?_,h⟩,rfl⟩)
  by_contra hw
  have hn := Binary64.out_of_range w (not_lt.mp hw)
  rw [h] at hn
  contradiction

/-- Successful Word decoding fixes a finite value; no native transport is inferred. -/
theorem decoded_fixed {w : Binary64.Word} {q : ℚ} (h : Binary64.decode w = some q) :
    down binaryValues ((q:ℝ):EReal) = ((q:ℝ):EReal) ∧
      up binaryValues ((q:ℝ):EReal) = ((q:ℝ):EReal) := fixed (decoded_representable h)

/-- Every existing finite Word enclosure certificate contains the mathematical
least representable enclosure. It need not equal it. The empty case is vacuous. -/
theorem word_certificate {S : Set ℝ} {O : HardwareAddition.Bounds Binary64.Word}
    (he : ∀ x ∈ S, HardwareAddition.Contains Binary64.real O x) :
    ∀ x ∈ hull binaryValues S, HardwareAddition.Contains Binary64.real O x := by
  by_cases hn : S.Nonempty
  · obtain ⟨v,hv⟩ := hn
    obtain ⟨l,u,hl,hu,_⟩ := he v hv
    obtain ⟨ql,hql,el⟩ : ∃ q, Binary64.decode O.lo = some q ∧ (q:ℝ)=l := by
      cases hd : Binary64.decode O.lo with
      | none => simp [Binary64.real,hd] at hl
      | some q => exact ⟨q,rfl,by simpa [Binary64.real,hd] using hl⟩
    obtain ⟨qu,hqu,eu⟩ : ∃ q, Binary64.decode O.hi = some q ∧ (q:ℝ)=u := by
      cases hd : Binary64.decode O.hi with
      | none => simp [Binary64.real,hd] at hu
      | some q => exact ⟨q,rfl,by simpa [Binary64.real,hd] using hu⟩
    have hb : S ⊆ ExtendedImageHull.interval ((ql:ℝ):EReal) ((qu:ℝ):EReal) := by
      intro z hz
      obtain ⟨l',u',hl',hu',hz'⟩ := he z hz
      have el' : l'=l := Option.some.inj (hl'.symm.trans hl)
      have eu' : u'=u := Option.some.inj (hu'.symm.trans hu)
      exact ⟨EReal.coe_le_coe_iff.mpr (by simpa [el,el'] using hz'.1),
        EReal.coe_le_coe_iff.mpr (by simpa [eu,eu'] using hz'.2)⟩
    intro x hx
    have h := least (decoded_representable hql) (decoded_representable hqu) hb hx
    exact ⟨l,u,hl,hu,by simpa [el] using EReal.coe_le_coe_iff.mp h.1,
      by simpa [eu] using EReal.coe_le_coe_iff.mp h.2⟩
  · have hs : S=∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [hs,empty]

/-- Reuse the prior observed directed-addition contract; no least-rounding
premise or success promise is added. -/
theorem observed_addition (I J : QInterval) {A B O : HardwareAddition.Bounds Binary64.Word}
    (ha0 : Binary64.real A.lo = some (I.lo:ℝ)) (ha1 : Binary64.real A.hi = some (I.hi:ℝ))
    (hb0 : Binary64.real B.lo = some (J.lo:ℝ)) (hb1 : Binary64.real B.hi = some (J.hi:ℝ))
    {lower upper : Option (Binary64.Word × Binary64.Word)}
    (hl : HardwareAddition.CallSound Binary64.real A.lo B.lo lower)
    (hu : HardwareAddition.CallSound Binary64.real A.hi B.hi upper)
    (hs : HardwareAddition.assemble lower upper = some O) :
    ∀ z ∈ hull binaryValues (ExactImageHull.sums I J), HardwareAddition.Contains Binary64.real O z := by
  apply word_certificate
  intro z hz
  exact ExactImageHull.hardware_add_contains_hull I J ha0 ha1 hb0 hb1 hl hu hs z
    (by rw [ExactImageHull.add_exact]; exact ExactImageHull.sums_enclosed I J hz)

end GeneralizedIntervalArithmetic.DiscreteDemotion
