import LinearMultiplication

namespace GeneralizedIntervalArithmetic

/-- A conservative reciprocal fallback: forget denominator dependence only after
its whole hull excludes zero. Failure is unknown, not a claim of undefinedness. -/
def LinearInterval.recip? (J : LinearInterval) : Option LinearInterval :=
  if h : J.hull.AwayZero then some (.constant (J.hull.recip h)) else none

def LinearInterval.div? (I J : LinearInterval) : Option LinearInterval :=
  (J.recip?).map (fun R => I.mul R)

theorem linear_recip_success_iff (J : LinearInterval) :
    J.recip?.isSome ↔ J.hull.AwayZero := by
  simp only [LinearInterval.recip?]
  split <;> simp_all

theorem linear_recip_nonzero {J R : LinearInterval} {t y : ℝ}
    (hr : J.recip? = some R) (ht : t ∈ Set.Icc (0:ℝ) 1) (hy : J.Contains t y) : y ≠ 0 := by
  unfold LinearInterval.recip? at hr
  split at hr
  · rename_i h
    exact awayZero_nonzero h (linear_hull_encloses ht hy)
  · cases hr

theorem linear_recip_encloses {J R : LinearInterval} {t y : ℝ}
    (hr : J.recip? = some R) (ht : t ∈ Set.Icc (0:ℝ) 1) (hy : J.Contains t y) :
    R.Contains t y⁻¹ := by
  unfold LinearInterval.recip? at hr
  split at hr
  · rename_i h
    cases Option.some.inj hr
    exact (linear_constant_contains _ _ _).mpr (recip_encloses h (linear_hull_encloses ht hy))
  · cases hr

private theorem linear_div_some {I J R : LinearInterval} (hr : I.div? J = some R) :
    ∃ S, J.recip? = some S ∧ I.mul S = R := by
  unfold LinearInterval.div? at hr
  cases hs : J.recip? with
  | none => simp [hs] at hr
  | some S => exact ⟨S, rfl, Option.some.inj (by simpa [hs] using hr)⟩

theorem linear_div_nonzero {I J R : LinearInterval} {t y : ℝ}
    (hr : I.div? J = some R) (ht : t ∈ Set.Icc (0:ℝ) 1) (hy : J.Contains t y) : y ≠ 0 := by
  obtain ⟨S, hs, _⟩ := linear_div_some hr
  exact linear_recip_nonzero hs ht hy

theorem linear_div_encloses {I J R : LinearInterval} {t x y : ℝ}
    (hr : I.div? J = some R) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hx : I.Contains t x) (hy : J.Contains t y) : R.Contains t (x/y) := by
  obtain ⟨S, hs, rfl⟩ := linear_div_some hr
  simpa [div_eq_mul_inv] using linear_mul_encloses ht hx (linear_recip_encloses hs ht hy)

/-- The nonzero denominator is part of the relation, not a totalized convention. -/
def QuotientValues {α : Type*} (A B : α → ℝ → Prop) (p : α) (z : ℝ) : Prop :=
  ∃ x y, A p x ∧ B p y ∧ y ≠ 0 ∧ z = x/y

theorem linear_div_domain_sound {I J R : LinearInterval} {D E : DomainBounds ℝ}
    {A B : ℝ → ℝ → Prop} (hI : (I.onDomain D).Sound A)
    (hJ : (J.onDomain E).Sound B) (hr : I.div? J = some R) :
    (R.onDomain (D.inter E)).Sound (QuotientValues A B) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro t z ⟨x, y, hx, hy, _, rfl⟩
    exact linear_div_encloses hr (hI.2.1 t x hx).1 (hI.1 t x hx) (hJ.1 t y hy)
  · rintro t z ⟨x, y, hx, hy, _, _⟩
    exact ⟨(hI.2.1 t x hx).1, (hI.2.1 t x hx).2, (hJ.2.1 t y hy).2⟩
  · intro t ht
    obtain ⟨x, hx⟩ := hI.2.2 t ⟨ht.1, ht.2.1⟩
    obtain ⟨y, hy⟩ := hJ.2.2 t ⟨ht.1, ht.2.2⟩
    exact ⟨x/y, x, y, hx, hy, linear_div_nonzero hr ht.1 (hJ.1 t y hy), rfl⟩

end GeneralizedIntervalArithmetic
