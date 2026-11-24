import DiscreteDemotion
import Mathlib.Data.Int.Interval

namespace GeneralizedIntervalArithmetic.FiniteFormat

/-- Literal finite coefficient format of Tupper §2.5, not an IEEE encoding. -/
structure Format where
  radix : ℕ
  precision : ℕ
  minExponent : ℤ
  maxExponent : ℤ
  radix_ge_two : 2 ≤ radix
  precision_pos : 0 < precision
  exponents_ordered : minExponent ≤ maxExponent

def bound (F : Format) : ℤ := (F.radix : ℤ) ^ (F.precision - 1)
def shift (F : Format) : ℤ := (F.precision - 1 : ℕ)
def value (F : Format) (a c : ℤ) : ℚ := (a : ℚ) * (F.radix : ℚ) ^ c

def values (F : Format) : Finset ℚ :=
  ((Finset.Ioo (-(bound F)) (bound F)).product
    (Finset.Icc (F.minExponent - (shift F)) (F.maxExponent - (shift F)))).image
    (fun ac => (value F) ac.1 ac.2)

theorem mem_values (F : Format) (q : ℚ) : q ∈ (values F) ↔
    ∃ a c : ℤ, -(bound F) < a ∧ a < (bound F) ∧
      F.minExponent ≤ c + (shift F) ∧ c + (shift F) ≤ F.maxExponent ∧ q = (value F) a c := by
  rw [values, Finset.mem_image]
  constructor
  · rintro ⟨⟨a,c⟩,hac,hq⟩
    have h := Finset.mem_product.mp hac
    simp only [Finset.mem_Ioo, Finset.mem_Icc] at h
    exact ⟨a,c,h.1.1,h.1.2,by omega,by omega,hq.symm⟩
  · rintro ⟨a,c,ha,hb,hc,hd,hq⟩
    refine ⟨(a,c),Finset.mem_product.mpr ⟨?_,?_⟩,hq.symm⟩
    · exact Finset.mem_Ioo.mpr ⟨ha,hb⟩
    · exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩

theorem zero_mem (F : Format) : 0 ∈ (values F) := by
  apply (mem_values F 0).mpr
  have hb : 0 < (bound F) := by
    unfold bound
    apply pow_pos
    have := F.radix_ge_two
    exact_mod_cast (by omega : 0 < F.radix)
  refine ⟨0,F.minExponent-(shift F),by omega,hb,by omega,?_,?_⟩
  · have := F.exponents_ordered; omega
  · simp [value]

/-- Real in-range means bracketed by finite represented values. -/
def InRange (F : Format) (x : ℝ) : Prop :=
  ∃ l ∈ (values F), ∃ u ∈ (values F), (l:ℝ) ≤ x ∧ x ≤ (u:ℝ)

/-- The existing extremal demotion has finite represented endpoints in range. -/
theorem finite_directed (F : Format) {x : ℝ} (hx : (InRange F) x) :
    ∃ l ∈ (values F), ∃ u ∈ (values F),
      DiscreteDemotion.down (values F) (x:EReal) = ((l:ℝ):EReal) ∧
      DiscreteDemotion.up (values F) (x:EReal) = ((u:ℝ):EReal) ∧
      (l:ℝ) ≤ x ∧ x ≤ (u:ℝ) := by
  obtain ⟨a,ha,b,hb,hax,hxb⟩ := hx
  have ea := (DiscreteDemotion.mem_endpoints (values F) ((a:ℝ):EReal)).mpr (Or.inr (Or.inr ⟨a,ha,rfl⟩))
  have eb := (DiscreteDemotion.mem_endpoints (values F) ((b:ℝ):EReal)).mpr (Or.inr (Or.inr ⟨b,hb,rfl⟩))
  have hd := DiscreteDemotion.down_spec (values F) (x:EReal)
  have hu := DiscreteDemotion.up_spec (values F) (x:EReal)
  have hda := DiscreteDemotion.down_greatest ea (EReal.coe_le_coe_iff.mpr hax)
  have hub := DiscreteDemotion.up_least eb (EReal.coe_le_coe_iff.mpr hxb)
  rcases (DiscreteDemotion.mem_endpoints _ _).mp hd.1 with h | h | ⟨l,hl,el⟩
  · rw [h] at hda; simp at hda
  · rw [h] at hd; simp at hd
  · rcases (DiscreteDemotion.mem_endpoints _ _).mp hu.1 with h | h | ⟨u,hu',eu⟩
    · rw [h] at hu; simp at hu
    · rw [h] at hub; simp at hub
    · exact ⟨l,hl,u,hu',el,eu,
        EReal.coe_le_coe_iff.mp (el ▸ hd.2),EReal.coe_le_coe_iff.mp (eu ▸ hu.2)⟩

/-- Soundness and minimality against every represented finite enclosing pair. -/
theorem enclosure_least (F : Format) (x : ℝ) {a b : ℚ}
    (ha : a ∈ (values F)) (hb : b ∈ (values F)) (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ)) :
    x ∈ ExtendedImageHull.interval (DiscreteDemotion.down (values F) (x:EReal))
      (DiscreteDemotion.up (values F) (x:EReal)) ∧
    ExtendedImageHull.interval (DiscreteDemotion.down (values F) (x:EReal))
      (DiscreteDemotion.up (values F) (x:EReal)) ⊆ Set.Icc (a:ℝ) (b:ℝ) := by
  refine ⟨⟨(DiscreteDemotion.down_spec _ _).2,(DiscreteDemotion.up_spec _ _).2⟩,?_⟩
  intro z hz
  have hl := DiscreteDemotion.down_greatest
    ((DiscreteDemotion.mem_endpoints _ _).mpr (Or.inr (Or.inr ⟨a,ha,rfl⟩)))
    (EReal.coe_le_coe_iff.mpr hax)
  have hu := DiscreteDemotion.up_least
    ((DiscreteDemotion.mem_endpoints _ _).mpr (Or.inr (Or.inr ⟨b,hb,rfl⟩)))
    (EReal.coe_le_coe_iff.mpr hxb)
  exact ⟨EReal.coe_le_coe_iff.mp (hl.trans hz.1),EReal.coe_le_coe_iff.mp (hz.2.trans hu)⟩

/-- Rational extremum certificates identify the existing real-order demotion. -/
theorem rational_down (F : Format) {a x : ℚ} (ha : a ∈ values F) (hax : a ≤ x)
    (hbest : ∀ q ∈ values F, q ≤ x → q ≤ a) :
    DiscreteDemotion.down (values F) ((x:ℝ):EReal) = ((a:ℝ):EReal) := by
  apply DiscreteDemotion.down_eq
  · exact (DiscreteDemotion.mem_endpoints _ _).mpr (Or.inr (Or.inr ⟨a,ha,rfl⟩))
  · exact_mod_cast hax
  · intro v hv hx
    rcases (DiscreteDemotion.mem_endpoints _ _).mp hv with rfl | rfl | ⟨q,hq,rfl⟩
    · exact bot_le
    · simp at hx
    · have hqx : q ≤ x := by exact_mod_cast hx
      exact_mod_cast hbest q hq hqx

theorem rational_up (F : Format) {a x : ℚ} (ha : a ∈ values F) (hxa : x ≤ a)
    (hbest : ∀ q ∈ values F, x ≤ q → a ≤ q) :
    DiscreteDemotion.up (values F) ((x:ℝ):EReal) = ((a:ℝ):EReal) := by
  apply DiscreteDemotion.up_eq
  · exact (DiscreteDemotion.mem_endpoints _ _).mpr (Or.inr (Or.inr ⟨a,ha,rfl⟩))
  · exact_mod_cast hxa
  · intro v hv hx
    rcases (DiscreteDemotion.mem_endpoints _ _).mp hv with rfl | rfl | ⟨q,hq,rfl⟩
    · simp at hx
    · exact le_top
    · have hxq : x ≤ q := by exact_mod_cast hx
      exact_mod_cast hbest q hq hxq

/-- Certificate bridge: decoded Word endpoints must separately belong to this
format. No equality with the binary64 value family or native refinement assumed. -/
theorem word_enclosure (F : Format) {l u : Binary64.Word} {a b : ℚ}
    (hl : Binary64.decode l = some a) (hu : Binary64.decode u = some b)
    (ha : a ∈ (values F)) (hb : b ∈ (values F)) {S : Set ℝ}
    (h : ∀ x ∈ S, (a:ℝ) ≤ x ∧ x ≤ (b:ℝ)) :
    ∀ x ∈ DiscreteDemotion.hull (values F) S,
      HardwareAddition.Contains Binary64.real ⟨l,u⟩ x := by
  have he : S ⊆ ExtendedImageHull.interval ((a:ℝ):EReal) ((b:ℝ):EReal) :=
    fun x hx => ⟨EReal.coe_le_coe_iff.mpr (h x hx).1,EReal.coe_le_coe_iff.mpr (h x hx).2⟩
  have hh := DiscreteDemotion.least
    ((DiscreteDemotion.mem_endpoints _ _).mpr (Or.inr (Or.inr ⟨a,ha,rfl⟩)))
    ((DiscreteDemotion.mem_endpoints _ _).mpr (Or.inr (Or.inr ⟨b,hb,rfl⟩))) he
  intro x hx
  exact ⟨a,b,by simp [Binary64.real,hl],by simp [Binary64.real,hu],
    EReal.coe_le_coe_iff.mp (hh hx).1,EReal.coe_le_coe_iff.mp (hh hx).2⟩
end GeneralizedIntervalArithmetic.FiniteFormat
