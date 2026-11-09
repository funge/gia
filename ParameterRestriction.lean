import GuardedEvaluator
import Mathlib.Tactic.FieldSimp

namespace GeneralizedIntervalArithmetic

/-- A closed rational subinterval of the certified unit parameter range.
Degenerate cells are permitted. -/
structure ParameterCell where
  interval : QInterval
  nonneg : 0 ≤ interval.lo
  le_one : interval.hi ≤ 1

noncomputable def ParameterCell.map (C : ParameterCell) (s : ℝ) : ℝ :=
  (1-s)*(C.interval.lo:ℝ) + s*C.interval.hi

theorem parameter_map_mem (C : ParameterCell) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    C.interval.Contains (C.map s) := by
  have ho : (C.interval.lo:ℝ) ≤ C.interval.hi := by exact_mod_cast C.interval.ordered
  change (C.interval.lo:ℝ) ≤ (1-s)*(C.interval.lo:ℝ)+s*C.interval.hi ∧
    (1-s)*(C.interval.lo:ℝ)+s*C.interval.hi ≤ C.interval.hi
  have h0 := mul_nonneg hs.1 (sub_nonneg.mpr ho)
  have h1 := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr ho)
  constructor <;> nlinarith

theorem parameter_map_unit (C : ParameterCell) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    C.map s ∈ Set.Icc (0:ℝ) 1 := by
  have h := parameter_map_mem C hs
  have hn : (0:ℝ) ≤ C.interval.lo := by exact_mod_cast C.nonneg
  have hu : (C.interval.hi:ℝ) ≤ 1 := by exact_mod_cast C.le_one
  exact ⟨hn.trans h.1,h.2.trans hu⟩

/-- Includes both endpoints and collapsed cells; no division by a zero width. -/
theorem parameter_map_onto (C : ParameterCell) {t : ℝ} (ht : C.interval.Contains t) :
    ∃ s ∈ Set.Icc (0:ℝ) 1, C.map s = t := by
  have ho : (C.interval.lo:ℝ) ≤ C.interval.hi := by exact_mod_cast C.interval.ordered
  rcases eq_or_lt_of_le ho with he | hp
  · refine ⟨0,by norm_num,?_⟩
    have h : t = C.interval.lo := le_antisymm (he ▸ ht.2) ht.1
    simpa [ParameterCell.map] using h.symm
  · have hd : (0:ℝ) < C.interval.hi - C.interval.lo := sub_pos.mpr hp
    refine ⟨(t-C.interval.lo)/(C.interval.hi-C.interval.lo),⟨?_,?_⟩,?_⟩
    · exact div_nonneg (sub_nonneg.mpr ht.1) hd.le
    · apply (div_le_one hd).mpr
      linarith [ht.2]
    · unfold ParameterCell.map
      field_simp
      nlinarith

def QAffine.reparam (a : QAffine) (C : ParameterCell) : QAffine :=
  ⟨(1-C.interval.lo)*a.atZero+C.interval.lo*a.atOne,
   (1-C.interval.hi)*a.atZero+C.interval.hi*a.atOne⟩

theorem affine_reparam_value (a : QAffine) (C : ParameterCell) (s : ℝ) :
    (a.reparam C).value s = a.value (C.map s) := by
  simp [QAffine.value,QAffine.reparam,ParameterCell.map]
  ring

def LinearInterval.reparam (I : LinearInterval) (C : ParameterCell) : LinearInterval :=
  ⟨I.lower.reparam C,I.upper.reparam C,
    add_le_add (mul_le_mul_of_nonneg_left I.orderedZero
      (sub_nonneg.mpr (C.interval.ordered.trans C.le_one)))
      (mul_le_mul_of_nonneg_left I.orderedOne C.nonneg),
    add_le_add (mul_le_mul_of_nonneg_left I.orderedZero (sub_nonneg.mpr C.le_one))
      (mul_le_mul_of_nonneg_left I.orderedOne (C.nonneg.trans C.interval.ordered))⟩

/-- Exact pointwise correspondence, not an approximate hull conversion. -/
theorem linear_reparam_contains (I : LinearInterval) (C : ParameterCell) (s z : ℝ) :
    (I.reparam C).Contains s z ↔ I.Contains (C.map s) z := by
  simp only [LinearInterval.Contains,LinearInterval.reparam,affine_reparam_value]

/-- Precompose domain predicates; onDomain supplies the new unit-range boundary. -/
def ParameterCell.pullDomain (C : ParameterCell) (D : DomainBounds ℝ) : DomainBounds ℝ :=
  ⟨fun s => D.definite (C.map s),fun s => D.possible (C.map s),
   fun s h => D.consistent (C.map s) h⟩

theorem linear_reparam_domain_sound {I : LinearInterval} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} (h : (I.onDomain D).Sound R) (C : ParameterCell) :
    ((I.reparam C).onDomain (C.pullDomain D)).Sound
      (fun s z => s ∈ Set.Icc (0:ℝ) 1 ∧ R (C.map s) z) := by
  refine ⟨?_,?_,?_⟩
  · rintro s z ⟨_,hz⟩
    exact (linear_reparam_contains I C s z).mpr (h.1 _ _ hz)
  · rintro s z ⟨hs,hz⟩
    exact ⟨hs,(h.2.1 _ _ hz).2⟩
  · intro s hs
    obtain ⟨z,hz⟩ := h.2.2 _ ⟨parameter_map_unit C hs.1,hs.2⟩
    exact ⟨z,hs.1,hz⟩

/-- Supplied finite closed cover. No new subdivision/search policy is introduced. -/
def ParameterCover (cells : List ParameterCell) : Prop :=
  ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ C ∈ cells, C.interval.Contains t

theorem parameter_cover_pullback {cells : List ParameterCell} (hc : ParameterCover cells)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃ C ∈ cells, ∃ s ∈ Set.Icc (0:ℝ) 1, C.map s = t := by
  obtain ⟨C,hC,hmem⟩ := hc t ht
  obtain ⟨s,hs,he⟩ := parameter_map_onto C hmem
  exact ⟨C,hC,s,hs,he⟩

/-- Universal semantic claims established on every covered cell transfer back.
No existential witness or continuity is manufactured by a coverage proof. -/
theorem parameter_cover_transfer {cells : List ParameterCell} (hc : ParameterCover cells)
    {R : ℝ → ℝ → Prop} {P : ℝ → ℝ → Prop}
    (hlocal : ∀ C ∈ cells, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ z,
      R (C.map s) z → P (C.map s) z)
    {t z : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hz : R t z) : P t z := by
  obtain ⟨C,hC,s,hs,he⟩ := parameter_cover_pullback hc ht
  simpa [he] using hlocal C hC s hs z (he.symm ▸ hz)

/-- Evaluate on numerically restricted coordinates while transporting their
actual partial relations and domain predicates, without assuming total inputs. -/
theorem evalGuarded_reparam_relational_sound
    {X Y R : LinearInterval} {D E : DomainBounds ℝ} {A B : ℝ → ℝ → Prop}
    {e : Expr} (C : ParameterCell)
    (hX : (X.onDomain D).Sound A) (hY : (Y.onDomain E).Sound B)
    (hr : evalGuarded (X.reparam C) (Y.reparam C) e = some R) :
    (R.onDomain ((C.pullDomain D).inter (C.pullDomain E))).Sound
      (fun s z => s ∈ Set.Icc (0:ℝ) 1 ∧ ExpressionValues A B e (C.map s) z) := by
  have hc := evalGuarded_relational_sound (linear_reparam_domain_sound hX C)
    (linear_reparam_domain_sound hY C) hr
  refine ⟨?_,?_,?_⟩
  · rintro s z ⟨hs,x,y,hx,hy,hv⟩
    exact hc.1 s z ⟨x,y,⟨hs,hx⟩,⟨hs,hy⟩,hv⟩
  · rintro s z ⟨hs,x,y,hx,hy,hv⟩
    exact hc.2.1 s z ⟨x,y,⟨hs,hx⟩,⟨hs,hy⟩,hv⟩
  · intro s hs
    obtain ⟨z,x,y,hx,hy,hv⟩ := hc.2.2 s hs
    exact ⟨z,hx.1,x,y,hx.2,hy.2,hv⟩

end GeneralizedIntervalArithmetic
