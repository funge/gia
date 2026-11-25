import FiniteFormat
import PartialRealArithmetic

namespace GeneralizedIntervalArithmetic.DirectedOperationAlgebra
open DiscreteDemotion

/-- Only finite decoded results. Out-of-range is failure of this relation,
not a specification of overflow to a literal infinity or lambda. -/
def Rounded (D : Finset ℚ) (x : ℝ) (l u : ℚ) : Prop :=
  l ∈ D ∧ u ∈ D ∧ down D (x:EReal) = ((l:ℝ):EReal) ∧
    up D (x:EReal) = ((u:ℝ):EReal)
def InRange (D : Finset ℚ) (x : ℝ) : Prop :=
  ∃ l ∈ D, ∃ u ∈ D, (l:ℝ) ≤ x ∧ x ≤ (u:ℝ)

/-- Rounding cannot invent an absent operation value. -/
def Operation {α : Type*} (D : Finset ℚ) (R : α → ℝ → Prop)
    (a : α) (l u : ℚ) : Prop := ∃ x, R a x ∧ Rounded D x l u

theorem rounded_sound {D : Finset ℚ} {x : ℝ} {l u : ℚ}
    (h : Rounded D x l u) : (l:ℝ) ≤ x ∧ x ≤ (u:ℝ) := by
  have hd := (down_spec D (x:EReal)).2
  have hu := (up_spec D (x:EReal)).2
  rw [h.2.2.1] at hd
  rw [h.2.2.2] at hu
  exact ⟨EReal.coe_le_coe_iff.mp hd,EReal.coe_le_coe_iff.mp hu⟩

theorem rounded_exists_iff (D : Finset ℚ) (x : ℝ) :
    (∃ l u, Rounded D x l u) ↔ InRange D x := by
  constructor
  · rintro ⟨l,u,h⟩
    exact ⟨l,h.1,u,h.2.1,rounded_sound h⟩
  · rintro ⟨a,ha,b,hb,hax,hxb⟩
    have ea := (mem_endpoints D ((a:ℝ):EReal)).mpr (Or.inr (Or.inr ⟨a,ha,rfl⟩))
    have eb := (mem_endpoints D ((b:ℝ):EReal)).mpr (Or.inr (Or.inr ⟨b,hb,rfl⟩))
    have hd := down_spec D (x:EReal)
    have hu := up_spec D (x:EReal)
    have hda := down_greatest ea (EReal.coe_le_coe_iff.mpr hax)
    have hub := up_least eb (EReal.coe_le_coe_iff.mpr hxb)
    rcases (mem_endpoints _ _).mp hd.1 with h | h | ⟨l,hl,el⟩
    · rw [h] at hda; simp at hda
    · rw [h] at hd; simp at hd
    · rcases (mem_endpoints _ _).mp hu.1 with h | h | ⟨u,hu',eu⟩
      · rw [h] at hu; simp at hu
      · rw [h] at hub; simp at hub
      · exact ⟨l,u,hl,hu',el,eu⟩

/-- Exact extremal certificate, stronger than mere outward containment. -/
theorem rounded_iff_extremal (D : Finset ℚ) (x : ℝ) (l u : ℚ) :
    Rounded D x l u ↔ l ∈ D ∧ u ∈ D ∧ (l:ℝ) ≤ x ∧ x ≤ (u:ℝ) ∧
      (∀ q ∈ D, (q:ℝ) ≤ x → q ≤ l) ∧
      (∀ q ∈ D, x ≤ (q:ℝ) → u ≤ q) := by
  constructor
  · intro h
    refine ⟨h.1,h.2.1,(rounded_sound h).1,(rounded_sound h).2,?_,?_⟩
    · intro q hq hx
      have hh := down_greatest ((mem_endpoints D _).mpr (Or.inr (Or.inr ⟨q,hq,rfl⟩)))
        (EReal.coe_le_coe_iff.mpr hx)
      rw [h.2.2.1] at hh
      exact_mod_cast (EReal.coe_le_coe_iff.mp hh)
    · intro q hq hx
      have hh := up_least ((mem_endpoints D _).mpr (Or.inr (Or.inr ⟨q,hq,rfl⟩)))
        (EReal.coe_le_coe_iff.mpr hx)
      rw [h.2.2.2] at hh
      exact_mod_cast (EReal.coe_le_coe_iff.mp hh)
  · rintro ⟨hl,hu,hlo,hhi,hmax,hmin⟩
    refine ⟨hl,hu,?_,?_⟩
    · apply down_eq ((mem_endpoints D _).mpr (Or.inr (Or.inr ⟨l,hl,rfl⟩)))
        (EReal.coe_le_coe_iff.mpr hlo)
      intro v hv hx
      rcases (mem_endpoints _ _).mp hv with rfl | rfl | ⟨q,hq,rfl⟩
      · exact bot_le
      · simp at hx
      · exact_mod_cast hmax q hq (EReal.coe_le_coe_iff.mp hx)
    · apply up_eq ((mem_endpoints D _).mpr (Or.inr (Or.inr ⟨u,hu,rfl⟩)))
        (EReal.coe_le_coe_iff.mpr hhi)
      intro v hv hx
      rcases (mem_endpoints _ _).mp hv with rfl | rfl | ⟨q,hq,rfl⟩
      · simp at hx
      · exact le_top
      · exact_mod_cast hmin q hq (EReal.coe_le_coe_iff.mp hx)

/-- Any finite represented enclosure contains the least rounded enclosure. -/
theorem rounded_least {D : Finset ℚ} {x : ℝ} {l u a b : ℚ}
    (h : Rounded D x l u) (ha : a ∈ D) (hb : b ∈ D)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ)) :
    Set.Icc (l:ℝ) (u:ℝ) ⊆ Set.Icc (a:ℝ) (b:ℝ) := by
  have hs := (rounded_iff_extremal D x l u).1 h
  have hl : (a:ℝ) ≤ (l:ℝ) := by exact_mod_cast hs.2.2.2.2.1 a ha hax
  have hu : (u:ℝ) ≤ (b:ℝ) := by exact_mod_cast hs.2.2.2.2.2 b hb hxb
  intro z hz
  exact ⟨hl.trans hz.1,hz.2.trans hu⟩

theorem rounded_unique {D : Finset ℚ} {x : ℝ} {l u a b : ℚ}
    (h : Rounded D x l u) (k : Rounded D x a b) : l=a ∧ u=b := by
  have hl := h.2.2.1.symm.trans k.2.2.1
  have hu := h.2.2.2.symm.trans k.2.2.2
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hu

theorem exact_representable {D : Finset ℚ} {q : ℚ} (h : q ∈ D) : Rounded D q q q :=
  ⟨h,h,fixed ((mem_endpoints D _).mpr (Or.inr (Or.inr ⟨q,h,rfl⟩)))⟩

theorem operation_domain {α : Type*} (D : Finset ℚ) (R : α → ℝ → Prop) (a : α) :
    (∃ l u, Operation D R a l u) ↔ ∃ x, R a x ∧ InRange D x := by
  constructor
  · rintro ⟨l,u,x,hx,hr⟩
    exact ⟨x,hx,(rounded_exists_iff D x).1 ⟨l,u,hr⟩⟩
  · rintro ⟨x,hx,hr⟩
    obtain ⟨l,u,h⟩ := (rounded_exists_iff D x).2 hr
    exact ⟨l,u,x,hx,h⟩

/-- The operation relation uses one result witness. For a functional partial
operation this encloses every actual result; nondeterministic images need a hull. -/
theorem operation_sound {α : Type*} {D : Finset ℚ} {R : α → ℝ → Prop}
    (hfun : ∀ a x y, R a x → R a y → x=y) {a : α} {l u : ℚ}
    (h : Operation D R a l u) {z : ℝ} (hz : R a z) :
    (l:ℝ) ≤ z ∧ z ≤ (u:ℝ) := by
  obtain ⟨x,hx,hr⟩ := h
  rw [←hfun a x z hx hz]
  exact rounded_sound hr

theorem operation_absent {α : Type*} {D : Finset ℚ} {R : α → ℝ → Prop} {a : α}
    (h : ¬∃x,R a x) (l u : ℚ) : ¬Operation D R a l u := by
  rintro ⟨x,hx,_⟩
  exact h ⟨x,hx⟩

theorem division_domain (D : Finset ℚ) (a b : ℝ) :
    (∃ l u, Operation D (fun p z => PartialRealArithmetic.divRel p.1 p.2 z) (a,b) l u) ↔
      b ≠ 0 ∧ InRange D (a/b) := by
  rw [operation_domain]
  simp [PartialRealArithmetic.divRel,PartialRealArithmetic.divDefined,PartialRealArithmetic.div]

theorem add_comm (D : Finset ℚ) (a b : ℝ) (l u : ℚ) :
    Rounded D (a+b) l u ↔ Rounded D (b+a) l u := by rw [_root_.add_comm a b]
theorem mul_comm (D : Finset ℚ) (a b : ℝ) (l u : ℚ) :
    Rounded D (a*b) l u ↔ Rounded D (b*a) l u := by rw [_root_.mul_comm a b]
theorem add_identity {D : Finset ℚ} {q : ℚ} (h : q ∈ D) : Rounded D ((q:ℝ)+0) q q := by
  simpa using exact_representable h
theorem mul_identity {D : Finset ℚ} {q : ℚ} (h : q ∈ D) : Rounded D ((q:ℝ)*1) q q := by
  simpa using exact_representable h
theorem add_cancellation {D : Finset ℚ} (h : 0 ∈ D) (x : ℝ) : Rounded D (x + -x) 0 0 := by
  simpa using exact_representable h
end GeneralizedIntervalArithmetic.DirectedOperationAlgebra
