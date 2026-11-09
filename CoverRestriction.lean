import CoverCoalescing
import ParameterRestriction

namespace GeneralizedIntervalArithmetic

/-- Reuse the existing exact affine change of parameter for every component. -/
def FiniteLinearCover.reparam (F : FiniteLinearCover) (C : ParameterCell) : FiniteLinearCover :=
  F.map (fun I => I.reparam C)

theorem cover_reparam_contains (F : FiniteLinearCover) (C : ParameterCell) (s z : ℝ) :
    (∃ I ∈ F.reparam C, I.Contains s z) ↔ ∃ I ∈ F, I.Contains (C.map s) z := by
  constructor
  · rintro ⟨I,hi,hz⟩
    obtain ⟨J,hj,rfl⟩ := List.mem_map.mp hi
    exact ⟨J,hj,(linear_reparam_contains J C s z).mp hz⟩
  · rintro ⟨I,hi,hz⟩
    exact ⟨I.reparam C,List.mem_map.mpr ⟨I,hi,rfl⟩,
      (linear_reparam_contains I C s z).mpr hz⟩

theorem cover_reparam_length (F : FiniteLinearCover) (C : ParameterCell) :
    (F.reparam C).length = F.length := by simp [FiniteLinearCover.reparam]

theorem cover_reparam_inclusion {F G : FiniteLinearCover} (h : F.IncludedIn G)
    (C : ParameterCell) : (F.reparam C).IncludedIn (G.reparam C) := by
  intro s hs z hz
  apply (cover_reparam_contains G C s z).mpr
  exact h (C.map s) (parameter_map_unit C hs) z ((cover_reparam_contains F C s z).mp hz)

theorem cover_reparam_domain_sound {F : FiniteLinearCover} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} (h : F.SoundOn D R) (C : ParameterCell) :
    (F.reparam C).SoundOn (C.pullDomain D)
      (fun s z => s ∈ Set.Icc (0:ℝ) 1 ∧ R (C.map s) z) := by
  refine ⟨?_,?_,?_⟩
  · rintro s z ⟨_,hz⟩
    exact (cover_reparam_contains F C s z).mpr (h.1 _ _ hz)
  · rintro s z ⟨hs,hz⟩
    exact ⟨hs,(h.2.1 _ _ hz).2⟩
  · intro s hs
    obtain ⟨z,hz⟩ := h.2.2 _ ⟨parameter_map_unit C hs.1,hs.2⟩
    exact ⟨z,hs.1,hz⟩

/-- Fresh evaluation on restricted coordinates may be sharper than restricting
an already evaluated cover. Both use the same pulled-back partial relations. -/
theorem evalConditionalCover_reparam_relational_sound
    {X Y : LinearInterval} {F : FiniteLinearCover} {D E : DomainBounds ℝ}
    {A B : ℝ → ℝ → Prop} {e : ConditionalExpr} (C : ParameterCell)
    (hX : (X.onDomain D).Sound A) (hY : (Y.onDomain E).Sound B)
    (hr : evalConditionalCover (X.reparam C) (Y.reparam C) e = some F) :
    F.SoundOn ((C.pullDomain D).inter (C.pullDomain E))
      (fun s z => s ∈ Set.Icc (0:ℝ) 1 ∧ ConditionalExpressionValues A B e (C.map s) z) := by
  have hc := evalConditionalCover_relational_sound
    (linear_reparam_domain_sound hX C) (linear_reparam_domain_sound hY C) hr
  refine ⟨?_,?_,?_⟩
  · rintro s z ⟨hs,x,y,hx,hy,hv⟩
    exact hc.1 s z ⟨x,y,⟨hs,hx⟩,⟨hs,hy⟩,hv⟩
  · rintro s z ⟨hs,x,y,hx,hy,hv⟩
    exact hc.2.1 s z ⟨x,y,⟨hs,hx⟩,⟨hs,hy⟩,hv⟩
  · intro s hs
    obtain ⟨z,x,y,hx,hy,hv⟩ := hc.2.2 s hs
    exact ⟨z,hx.1,x,y,hx.2,hy.2,hv⟩

end GeneralizedIntervalArithmetic
