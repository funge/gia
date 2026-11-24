import DedekindBoundary

/-! Tupper §2.15.1, printed pp.40–41: pointwise rational operations.
These are mathematical representatives, not an executable real-number backend. -/
namespace GeneralizedIntervalArithmetic.CutArithmetic
open DedekindBoundary

noncomputable def add (C D : Set ℚ) : Set ℚ := Set.image2 (· + ·) C D
noncomputable def mul (C D : Set ℚ) : Set ℚ := Set.image2 (· * ·) C D
noncomputable def Downward (C : Set ℚ) : Prop :=
  ∀ c∈C, ∀ q:ℚ, 0≤q → q<c → q∈C

/-- This derived decoded order compares upper-bound tests, not raw set inclusion. -/
theorem decoded_le_iff {C D : Set ℚ} {r s : ℝ}
    (hc : IsLUB (values C) r) (hd : IsLUB (values D) s) :
    r≤s ↔ ∀ u:ℝ, (∀ q∈D, (q:ℝ)≤u) → ∀ q∈C, (q:ℝ)≤u := by
  constructor
  · intro h u hu q hq
    exact (hc.1 ⟨q,hq,rfl⟩).trans (h.trans (hd.2 (by
      rintro x ⟨v,hv,rfl⟩; exact hu v hv)))
  · intro h
    apply hc.2
    rintro x ⟨q,hq,rfl⟩
    exact h s (fun v hv => hd.1 ⟨v,hv,rfl⟩) q hq

/-- Pointwise rational addition represents the sum, including unattained bounds. -/
theorem add_lub {C D : Set ℚ} {r s : ℝ}
    (hc : IsLUB (values C) r) (hd : IsLUB (values D) s) :
    IsLUB (values (add C D)) (r+s) := by
  constructor
  · rintro x ⟨q,⟨a,ha,b,hb,rfl⟩,rfl⟩
    push_cast
    exact add_le_add (hc.1 ⟨a,ha,rfl⟩) (hd.1 ⟨b,hb,rfl⟩)
  · intro u hu
    have hs : s≤u-r := hd.2 (by
      rintro y ⟨b,hb,rfl⟩
      have hr : r≤u-(b:ℝ) := hc.2 (by
        rintro x ⟨a,ha,rfl⟩
        have h := hu ⟨a+b,⟨a,ha,b,hb,rfl⟩,rfl⟩
        push_cast at h
        linarith)
      linarith)
    linarith

/-- Multiplication needs nonnegative admitted operands, as in the source.
The supplied lub premises exclude empty and unbounded representatives. -/
theorem mul_lub {C D : Set ℚ} {r s : ℝ}
    (hc : IsLUB (values C) r) (hd : IsLUB (values D) s)
    (hC : ∀ q∈C, 0≤q) (hD : ∀ q∈D, 0≤q) :
    IsLUB (values (mul C D)) (r*s) := by
  have hr : 0≤r := by
    obtain ⟨x,q,hq,rfl⟩ := hc.nonempty
    exact (show (0:ℝ)≤q by exact_mod_cast hC q hq).trans (hc.1 ⟨q,hq,rfl⟩)
  constructor
  · rintro x ⟨q,⟨a,ha,b,hb,rfl⟩,rfl⟩
    push_cast
    exact mul_le_mul (hc.1 ⟨a,ha,rfl⟩) (hd.1 ⟨b,hb,rfl⟩)
      (by exact_mod_cast hD b hb) hr
  · intro u hu
    apply (hd.mul_left hr).2
    rintro y ⟨x,⟨b,hb,rfl⟩,rfl⟩
    apply (hc.mul_right (show (0:ℝ)≤b by exact_mod_cast hD b hb)).2
    rintro z ⟨x,⟨a,ha,rfl⟩,rfl⟩
    have h := hu ⟨a*b,⟨a,ha,b,hb,rfl⟩,rfl⟩
    simpa using h

/-- Nonempty downward nonnegative representatives contain zero. -/
theorem zero_mem {C : Set ℚ} (hne : C.Nonempty)
    (hC : ∀ q∈C, 0≤q) (hd : Downward C) : 0∈C := by
  obtain ⟨q,hq⟩ := hne
  rcases eq_or_lt_of_le (hC q hq) with h|h
  · simpa [← h] using hq
  · exact hd q hq 0 le_rfl h

theorem add_downward {C D : Set ℚ} (hD : ∀ q∈D, 0≤q) (hc : Downward C) (hd : Downward D) :
    Downward (add C D) := by
  rintro z ⟨a,ha,b,hb,rfl⟩ q hq hlt
  dsimp at hlt
  by_cases hqa : q<a
  · exact ⟨q,hc a ha q hq hqa,0,zero_mem ⟨b,hb⟩ hD hd,by ring⟩
  · exact ⟨a,ha,q-a,hd b hb (q-a) (sub_nonneg.mpr (le_of_not_gt hqa))
      (by linarith),by ring⟩

theorem mul_downward {C D : Set ℚ} (hD : ∀ q∈D, 0≤q) (hc : Downward C) : Downward (mul C D) := by
  rintro z ⟨a,ha,b,hb,rfl⟩ q hq hlt
  dsimp at hlt
  have hbpos : 0<b := by
    rcases eq_or_lt_of_le (hD b hb) with h|h
    · rw [← h, mul_zero] at hlt; linarith
    · exact h
  exact ⟨q/b,hc a ha (q/b) (div_nonneg hq hbpos.le)
    ((div_lt_iff₀ hbpos).mpr hlt),b,hb,div_mul_cancel₀ q (ne_of_gt hbpos)⟩

/-- Encoded arithmetic stays nonnegative; a real lub makes each output proper. -/
theorem outputs_nonnegative {C D : Set ℚ}
    (hC : ∀q∈C,0≤q) (hD : ∀q∈D,0≤q) :
    (∀q∈add C D,0≤q) ∧ (∀q∈mul C D,0≤q) := by
  constructor
  · rintro q ⟨a,ha,b,hb,rfl⟩; exact add_nonneg (hC a ha) (hD b hb)
  · rintro q ⟨a,ha,b,hb,rfl⟩; exact mul_nonneg (hC a ha) (hD b hb)

theorem proper_of_lub {C : Set ℚ} {r : ℝ} (h : IsLUB (values C) r) :
    ∃b:ℚ, 0≤b ∧ b∉C := by
  obtain ⟨b,hb⟩ := exists_rat_gt (max r 0)
  refine ⟨b,by exact_mod_cast (le_max_right r 0).trans hb.le,?_⟩
  intro hc
  exact (not_le_of_gt ((le_max_left r 0).trans_lt hb)) (h.1 ⟨b,hc,rfl⟩)

/-- Independence of representative choice is decoded equality, not equality of sets. -/
theorem operations_representation_independent {C C' D D' : Set ℚ} {r s : ℝ}
    (hc : IsLUB (values C) r) (hc' : IsLUB (values C') r)
    (hd : IsLUB (values D) s) (hd' : IsLUB (values D') s)
    (hC : ∀q∈C,0≤q) (hC' : ∀q∈C',0≤q)
    (hD : ∀q∈D,0≤q) (hD' : ∀q∈D',0≤q) :
    sSup (values (add C D)) = sSup (values (add C' D')) ∧
    sSup (values (mul C D)) = sSup (values (mul C' D')) := by
  constructor
  · exact (add_lub hc hd).csSup_eq (add_lub hc hd).nonempty |>.trans
      ((add_lub hc' hd').csSup_eq (add_lub hc' hd').nonempty).symm
  · exact (mul_lub hc hd hC hD).csSup_eq (mul_lub hc hd hC hD).nonempty |>.trans
      ((mul_lub hc' hd' hC' hD').csSup_eq (mul_lub hc' hd' hC' hD').nonempty).symm

end GeneralizedIntervalArithmetic.CutArithmetic
