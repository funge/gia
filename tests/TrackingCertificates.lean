import TrackingCertificates
import AuditPolicy

namespace GeneralizedIntervalArithmetic.TrackingCertificatesChecks
open TrackingCertificates PartialProperties FiniteProperties DomainConstraints

noncomputable def reciprocal (v : Fin 1 → ℝ) : Option ℝ :=
  if v 0 = 0 then none else some (1 / v 0)
def coordinate (_i : Fin 1) : PartialReal := fun x => some x

theorem reciprocal_guard (x : ℝ) : OuterDefined reciprocal coordinate x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    obtain ⟨z, hz⟩ := h (fun _ => x) (fun _ => rfl)
    simp [reciprocal, hx] at hz
  · intro hx v hv
    have h0 : v 0 = x := (Option.some.inj (hv 0)).symm
    exact ⟨1 / v 0, by simp [reciprocal, h0, hx]⟩

/-- The actual definedness guard, not merely child definedness, is retained. -/
theorem guarded_description (x : ℝ) :
    (allDomains ((exactDomain (fun x : ℝ => x ≠ 0)) ::
      (List.finRange 1).map (fun _ => exactDomain (fun _ : ℝ => True)))).Compatible x
      (∃ z, composeN reciprocal coordinate x = some z) := by
  apply defined_description
  · intro i
    exact ⟨fun _ => ⟨x, rfl⟩, fun _ => trivial⟩
  · exact ⟨(reciprocal_guard x).mpr, (reciprocal_guard x).mp⟩

theorem zero_excluded : ¬ ∃ z, composeN reciprocal coordinate 0 = some z := by
  intro h
  have hd := (defined_factorization reciprocal coordinate 0).mp h
  exact ((reciprocal_guard 0).mp hd.2) rfl

theorem nonzero_included (x : ℝ) (hx : x ≠ 0) :
    composeN reciprocal coordinate x = some (1/x) := by
  apply (composeN_some _ _ _ _).mpr
  exact ⟨fun _ => x, fun _ => rfl, by simp [reciprocal, hx]⟩

theorem vacuous_outer_does_not_fill_hole :
    OuterDefined (fun _ : Fin 1 → ℝ => some 7) (fun _ _ => none) 0 ∧
    composeN (fun _ : Fin 1 → ℝ => some 7) (fun _ _ => none) 0 = none := by
  constructor
  · intro v hv
    have := hv 0
    contradiction
  · exact missing_input _ _ _ 0 rfl

theorem nullary_still_needs_outer :
    ¬ OuterDefined (fun _ : Fin 0 → ℝ => none) (fun i => Fin.elim0 i) 0 := by
  intro h
  obtain ⟨z, hz⟩ := h (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  contradiction

/-- Positive finite-arity certificate application reuses the existing theorem. -/
theorem positive_square_certificate :
    (sufficient (exactDomain (fun _ : Unit => True))).Compatible ()
      (ContinuousOnPartial (composeN (fun v : Fin 1 → ℝ => some ((v 0)^2)) coordinate) Set.univ) := by
  apply continuous_description (T := Set.univ)
  · exact ⟨fun _ i => ⟨id, continuous_id.continuousOn, fun _ _ => rfl⟩, fun _ => trivial⟩
  · exact ⟨fun v => (v 0)^2, ((continuous_apply 0).pow 2).continuousOn, fun _ _ => rfl⟩
  · exact fun _ _ _ _ => Set.mem_univ _

theorem failed_certificate_is_inconclusive :
    (sufficient (exactDomain (fun _ : Unit => False))).Compatible () True ∧
    (sufficient (exactDomain (fun _ : Unit => False))).Compatible () False :=
  ⟨no_possible_copy.2.2, ⟨False.elim, fun _ => trivial⟩⟩

open Filter
open scoped Topology

/-- Only the first coordinate is frozen. The second varies continuously. -/
theorem frozen_projection :
    LocallyConstantWithin
      (composeN (fun v : Fin 2 → ℝ => some (v 0))
        (fun i y => some (if i = 0 then 7 else y))) Set.univ 0 := by
  apply frozen_composeN (a := fun y i => if i = 0 then 7 else y)
    (v := fun i => if i = 0 then 7 else 0) (B := fun i => i = 0) (z := 7)
  · intro i; rfl
  · simp
  · exact Eventually.of_forall (fun _ _ => rfl)
  · have hc : Continuous (fun y : ℝ => fun i : Fin 2 => if i = 0 then 7 else y) := by
      apply continuous_pi
      intro i
      by_cases hi : i = 0
      · simp only [hi, if_true]; exact continuous_const
      · simp only [hi, if_false]; exact continuous_id
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · intro i hi
    subst i
    exact Eventually.of_forall (fun _ => rfl)
  · exact Eventually.of_forall (fun w hw => by simpa using congrArg some (hw 0 rfl))

/-- Freezing no coordinates cannot certify the identity as locally constant. -/
theorem identity_not_frozen :
    ¬ FrozenConstant (fun v : Fin 1 → ℝ => some (v 0))
      (fun _ => 0) (fun _ => False) 0 := by
  intro h
  have hc : Continuous (fun y : ℝ => (fun _ : Fin 1 => y)) := continuous_pi (fun _ => continuous_id)
  have hp : ∀ᶠ y : ℝ in nhds 0,
      (∀ i : Fin 1, False → y = 0) → some y = some (0:ℝ) := hc.continuousAt.tendsto h
  have he : ∀ᶠ y : ℝ in nhds 0, y = 0 :=
    hp.mono (fun y hy => Option.some.inj (hy (fun _ h => h.elim)))
  have hn := Metric.mem_nhds_iff.mp he
  obtain ⟨e, he, hall⟩ := hn
  have hh := hall (show e/2 ∈ Metric.ball (0:ℝ) e by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
    rw [abs_of_pos (by linarith)]
    linarith)
  change e/2 = 0 at hh
  linarith

end GeneralizedIntervalArithmetic.TrackingCertificatesChecks
#audit_namespace GeneralizedIntervalArithmetic.TrackingCertificatesChecks
