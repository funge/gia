import FiniteLinearCovers
import ConditionalEvaluator

namespace GeneralizedIntervalArithmetic

/-- Finite ranges with the existing definite/possible domain contract. The unit
parameter restriction is explicit, as in LinearInterval.onDomain. -/
def FiniteLinearCover.SoundOn (C : FiniteLinearCover) (D : DomainBounds ℝ)
    (R : ℝ → ℝ → Prop) : Prop :=
  (∀ t z, R t z → ∃ I ∈ C, I.Contains t z) ∧
  (∀ t z, R t z → t ∈ Set.Icc (0:ℝ) 1 ∧ D.possible t) ∧
  (∀ t, t ∈ Set.Icc (0:ℝ) 1 ∧ D.definite t → ∃ z, R t z)

theorem cover_soundOn_covers {C : FiniteLinearCover} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} (h : C.SoundOn D R) : C.Covers R :=
  fun t _ z hz => h.1 t z hz

theorem cover_domain_absent {C : FiniteLinearCover} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} (h : C.SoundOn D R) {t : ℝ}
    (ht : ¬ D.possible t) : ¬ ∃ z, R t z := by
  rintro ⟨z,hz⟩
  exact ht (h.2.1 t z hz).2

theorem cover_domain_definite {C : FiniteLinearCover} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} (h : C.SoundOn D R) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hd : D.definite t) : ∃ z, R t z :=
  h.2.2 t ⟨ht,hd⟩

/-- Successful reciprocation preserves both domain directions: all actual
input values are nonzero, not merely the selected examples. -/
theorem cover_recip_domain_sound {C F : FiniteLinearCover} {D : DomainBounds ℝ}
    {R : ℝ → ℝ → Prop} (h : C.SoundOn D R) (hr : C.recip? = some F) :
    F.SoundOn D (QuotientValues (fun _ z => z = 1) R) := by
  refine ⟨?_,?_,?_⟩
  · intro t z hz
    obtain ⟨x,y,hx,hy,hn,he⟩ := hz
    exact cover_recip_sound (cover_soundOn_covers h) hr t (h.2.1 t y hy).1 z
      ⟨x,y,hx,hy,hn,he⟩
  · rintro t z ⟨_,y,_,hy,_,_⟩
    exact h.2.1 t y hy
  · intro t ht
    obtain ⟨y,hy⟩ := h.2.2 t ht
    obtain ⟨I,hi,hI⟩ := h.1 t y hy
    obtain ⟨J,_,hj⟩ := cover_recip_member hr hi
    exact ⟨1/y,1,y,rfl,hy,linear_recip_nonzero hj ht.1 hI,rfl⟩

/-- Same certified lazy choices as evalConditional; unresolved alternatives
retain a union instead of joining their ranges. Failure remains unknown. -/
def evalConditionalCover (X Y : LinearInterval) : ConditionalExpr → Option FiniteLinearCover
  | .leaf e => (evalGuarded X Y e).map (fun I => [I])
  | .iteLt g q a b =>
    match evalGuarded X Y g with
    | none => none
    | some G => match decideLinearLt G q with
      | .yes => evalConditionalCover X Y a
      | .no => evalConditionalCover X Y b
      | .unknown => do
        let A ← evalConditionalCover X Y a
        let B ← evalConditionalCover X Y b
        pure (A ++ B)

theorem evalConditionalCover_success (X Y : LinearInterval) (e : ConditionalExpr) :
    (evalConditionalCover X Y e).isSome = (evalConditional X Y e).isSome := by
  induction e with
  | leaf e => simp [evalConditionalCover, evalConditional]
  | iteLt g q a b iha ihb =>
    simp only [evalConditionalCover, evalConditional]
    cases hg : evalGuarded X Y g with
    | none => rfl
    | some G =>
      cases hj : decideLinearLt G q with
      | yes => simpa [hj] using iha
      | no => simpa [hj] using ihb
      | unknown =>
        simp only [hj]
        cases ha : evalConditionalCover X Y a <;>
          cases hb : evalConditionalCover X Y b <;>
          cases hc : evalConditional X Y a <;>
          cases hd : evalConditional X Y b <;>
          simp_all [combineLinear]

private theorem append_some {a b : Option FiniteLinearCover} {C : FiniteLinearCover}
    (h : (do let A ← a; let B ← b; pure (A ++ B)) = some C) :
    ∃ A B, a = some A ∧ b = some B ∧ A ++ B = C := by
  cases a with
  | none => cases h
  | some A =>
    cases b with
    | none => cases h
    | some B => exact ⟨A,B,rfl,rfl,Option.some.inj h⟩

theorem evalConditionalCover_sound {X Y : LinearInterval} {C : FiniteLinearCover}
    {t x y z : ℝ} {e : ConditionalExpr}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hv : ConditionalValue x y e z) (hr : evalConditionalCover X Y e = some C) :
    ∃ I ∈ C, I.Contains t z := by
  induction hv generalizing C with
  | @leaf e z hv =>
    cases he : evalGuarded X Y e with
    | none => simp [evalConditionalCover,he] at hr
    | some I =>
      have hc : [I] = C := by simpa [evalConditionalCover,he] using hr
      subst C
      exact ⟨I,by simp,evalGuarded_sound ht hx hy hv he⟩
  | @yes g q a b u z hg hlt ha ih =>
    simp only [evalConditionalCover] at hr
    cases he : evalGuarded X Y g with
    | none => simp [he] at hr
    | some G =>
      have hu := evalGuarded_sound ht hx hy hg he
      simp only [he] at hr
      cases hc : decideLinearLt G q with
      | yes => exact ih (by simpa [hc] using hr)
      | no => exact (not_lt_of_ge (decision_no_le hc ht hu) hlt).elim
      | unknown =>
        obtain ⟨A,B,ha,_,rfl⟩ := append_some (by simpa [hc] using hr)
        obtain ⟨I,hi,hI⟩ := ih ha
        exact ⟨I,List.mem_append_left _ hi,hI⟩
  | @no g q a b u z hg hle hb ih =>
    simp only [evalConditionalCover] at hr
    cases he : evalGuarded X Y g with
    | none => simp [he] at hr
    | some G =>
      have hu := evalGuarded_sound ht hx hy hg he
      simp only [he] at hr
      cases hc : decideLinearLt G q with
      | yes => exact (not_lt_of_ge hle (decision_yes_lt hc ht hu)).elim
      | no => exact ih (by simpa [hc] using hr)
      | unknown =>
        obtain ⟨A,B,_,hb,rfl⟩ := append_some (by simpa [hc] using hr)
        obtain ⟨I,hi,hI⟩ := ih hb
        exact ⟨I,List.mem_append_right _ hi,hI⟩

theorem evalConditionalCover_defined {X Y : LinearInterval} {C : FiniteLinearCover}
    {t x y : ℝ} {e : ConditionalExpr}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hr : evalConditionalCover X Y e = some C) : ∃ z, ConditionalValue x y e z := by
  have hs := evalConditionalCover_success X Y e
  rw [hr] at hs
  cases he : evalConditional X Y e with
  | none => simp [he] at hs
  | some I => exact evalConditional_defined ht hx hy he

theorem evalConditionalCover_relational_sound {X Y : LinearInterval} {C : FiniteLinearCover}
    {D E : DomainBounds ℝ} {A B : ℝ → ℝ → Prop} {e : ConditionalExpr}
    (hX : (X.onDomain D).Sound A) (hY : (Y.onDomain E).Sound B)
    (hr : evalConditionalCover X Y e = some C) :
    C.SoundOn (D.inter E) (ConditionalExpressionValues A B e) := by
  refine ⟨?_,?_,?_⟩
  · rintro t z ⟨x,y,hx,hy,hv⟩
    exact evalConditionalCover_sound (hX.2.1 t x hx).1 (hX.1 t x hx) (hY.1 t y hy) hv hr
  · rintro t z ⟨x,y,hx,hy,_⟩
    exact ⟨(hX.2.1 t x hx).1,(hX.2.1 t x hx).2,(hY.2.1 t y hy).2⟩
  · intro t ht
    obtain ⟨x,hx⟩ := hX.2.2 t ⟨ht.1,ht.2.1⟩
    obtain ⟨y,hy⟩ := hY.2.2 t ⟨ht.1,ht.2.2⟩
    obtain ⟨z,hz⟩ := evalConditionalCover_defined ht.1 (hX.1 t x hx) (hY.1 t y hy) hr
    exact ⟨z,x,y,hx,hy,hz⟩

end GeneralizedIntervalArithmetic
