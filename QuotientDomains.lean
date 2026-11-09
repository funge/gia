import DomainQueries
import NonzeroDomains

namespace GeneralizedIntervalArithmetic

def QAffine.valueRat (a : QAffine) (q : ℚ) : ℚ := (1-q)*a.atZero + q*a.atOne

theorem affine_valueRat_cast (a : QAffine) (q : ℚ) :
    (a.valueRat q : ℝ) = a.value (q:ℝ) := by
  simp [QAffine.valueRat, QAffine.value]

/-- Rational refinement of the nonzero quotient-domain certificate. Both
operands use the same external domain; range bounds remain separate. -/
def quotientDomainRat (J : LinearInterval) (D : DomainBounds ℚ) : DomainBounds ℚ :=
  ⟨fun q => D.definite q ∧ (J.upper.valueRat q < 0 ∨ 0 < J.lower.valueRat q),
   fun q => D.possible q ∧ (J.lower.valueRat q ≠ 0 ∨ J.upper.valueRat q ≠ 0),
   fun q h => ⟨D.consistent q h.1, by
     rcases h.2 with h | h
     · exact Or.inr (ne_of_lt h)
     · exact Or.inl (ne_of_gt h)⟩⟩

noncomputable def LinearInterval.rationalPartial (I : LinearInterval)
    (D : DomainBounds ℚ) : PartialEnclosure ℚ :=
  ⟨⟨fun q => I.lower.value (q:ℝ), fun q => I.upper.value (q:ℝ)⟩, D⟩

theorem quotientDomainRat_definite (I J : LinearInterval) (D : DomainBounds ℚ) (q : ℚ) :
    (quotientDomainRat J D).definite q ↔
    ((I.rationalPartial D).quotientDomain (J.rationalPartial D)).definite q := by
  have h (a : QAffine) : a.valueRat q < 0 ↔ a.value (q:ℝ) < 0 := by
    rw [← affine_valueRat_cast]; exact_mod_cast Iff.rfl
  have k (a : QAffine) : 0 < a.valueRat q ↔ 0 < a.value (q:ℝ) := by
    rw [← affine_valueRat_cast]; exact_mod_cast Iff.rfl
  simp [quotientDomainRat, PartialEnclosure.quotientDomain, DomainBounds.inter,
    PartialEnclosure.nonzero, LinearInterval.rationalPartial, h, k]

theorem quotientDomainRat_possible (I J : LinearInterval) (D : DomainBounds ℚ) (q : ℚ) :
    (quotientDomainRat J D).possible q ↔
    ((I.rationalPartial D).quotientDomain (J.rationalPartial D)).possible q := by
  have h (a : QAffine) : a.valueRat q ≠ 0 ↔ a.value (q:ℝ) ≠ 0 := by
    rw [← affine_valueRat_cast]; exact_mod_cast Iff.rfl
  simp [quotientDomainRat, PartialEnclosure.quotientDomain, DomainBounds.inter,
    PartialEnclosure.nonzero, LinearInterval.rationalPartial, h]

/-- Unsupported syntax or failed child enclosure supplies no existence evidence.
External exclusion is retained even in this unknown arithmetic case. -/
def unresolvedDomain (D : DomainBounds ℚ) : DomainBounds ℚ :=
  ⟨fun _ => False, D.possible, fun _ h => h.elim⟩

/-- Restricted automatic construction: analyze one outer quotient, using the
existing guarded evaluator for both children. No alternative value evaluator. -/
def inferQuotientDomain (X Y : LinearInterval) (D : DomainBounds ℚ) : Expr → DomainBounds ℚ
  | .div a b => match evalGuarded X Y a, evalGuarded X Y b with
      | some _, some J => quotientDomainRat J D
      | _, _ => unresolvedDomain D
  | _ => unresolvedDomain D

instance quotientDomainRat_def_dec (J : LinearInterval) (D : DomainBounds ℚ) (q : ℚ)
    [Decidable (D.definite q)] : Decidable ((quotientDomainRat J D).definite q) :=
  inferInstanceAs (Decidable (D.definite q ∧ (J.upper.valueRat q < 0 ∨ 0 < J.lower.valueRat q)))
instance quotientDomainRat_poss_dec (J : LinearInterval) (D : DomainBounds ℚ) (q : ℚ)
    [Decidable (D.possible q)] : Decidable ((quotientDomainRat J D).possible q) :=
  inferInstanceAs (Decidable (D.possible q ∧ (J.lower.valueRat q ≠ 0 ∨ J.upper.valueRat q ≠ 0)))
instance unresolvedDomain_def_dec (D : DomainBounds ℚ) (q : ℚ) :
    Decidable ((unresolvedDomain D).definite q) := inferInstanceAs (Decidable False)
instance unresolvedDomain_poss_dec (D : DomainBounds ℚ) (q : ℚ)
    [Decidable (D.possible q)] : Decidable ((unresolvedDomain D).possible q) :=
  inferInstanceAs (Decidable (D.possible q))

instance inferQuotientDomain_def_dec (X Y : LinearInterval) (D : DomainBounds ℚ)
    (e : Expr) (q : ℚ) [Decidable (D.definite q)] :
    Decidable ((inferQuotientDomain X Y D e).definite q) := by
  cases e <;> simp only [inferQuotientDomain] <;> try infer_instance
  split <;> infer_instance
instance inferQuotientDomain_poss_dec (X Y : LinearInterval) (D : DomainBounds ℚ)
    (e : Expr) (q : ℚ) [Decidable (D.possible q)] :
    Decidable ((inferQuotientDomain X Y D e).possible q) := by
  cases e <;> simp only [inferQuotientDomain] <;> try infer_instance
  split <;> infer_instance

private theorem guarded_rational_sound {X Y I : LinearInterval} {D : DomainBounds ℚ}
    {E : ℚ → Prop} {x y : ℚ → ℝ} {e : Expr}
    (hp : ∀ q, E q → D.possible q) (hd : ∀ q, D.definite q → E q)
    (he : ∀ q, E q → (q:ℝ) ∈ Set.Icc (0:ℝ) 1 ∧
      X.Contains (q:ℝ) (x q) ∧ Y.Contains (q:ℝ) (y q))
    (hr : evalGuarded X Y e = some I) :
    (I.rationalPartial D).Sound (fun q z => E q ∧ Value (x q) (y q) e z) := by
  refine ⟨?_, fun q _ h => hp q h.1, ?_⟩
  · intro q z hz
    obtain ⟨ht, hx, hy⟩ := he q hz.1
    exact evalGuarded_sound ht hx hy hz.2 hr
  · intro q hq
    have hE := hd q hq
    obtain ⟨ht, hx, hy⟩ := he q hE
    obtain ⟨z, hz⟩ := evalGuarded_defined ht hx hy hr
    exact ⟨z, hE, hz⟩

private theorem quotient_relation {E : ℚ → Prop} {x y : ℚ → ℝ}
    (a b : Expr) (q : ℚ) (z : ℝ) :
    QuotientValues (fun q z => E q ∧ Value (x q) (y q) a z)
      (fun q z => E q ∧ Value (x q) (y q) b z) q z ↔
    E q ∧ Value (x q) (y q) (.div a b) z := by
  constructor
  · rintro ⟨u, v, ⟨hE, hu⟩, ⟨_, hv⟩, hn, rfl⟩
    exact ⟨hE, Value.div hu hv hn⟩
  · rintro ⟨hE, hv⟩
    cases hv with
    | div hu hv hn => exact ⟨_, _, ⟨hE, hu⟩, ⟨hE, hv⟩, hn, rfl⟩

/-- Actual values imply possible membership. Coordinates share one fixed pair
at each parameter, so independent quotient witnesses cannot mix environments. -/
theorem inferQuotientDomain_possible {X Y : LinearInterval} {D : DomainBounds ℚ}
    {E : ℚ → Prop} {x y : ℚ → ℝ}
    (hp : ∀ q, E q → D.possible q) (hd : ∀ q, D.definite q → E q)
    (he : ∀ q, E q → (q:ℝ) ∈ Set.Icc (0:ℝ) 1 ∧
      X.Contains (q:ℝ) (x q) ∧ Y.Contains (q:ℝ) (y q))
    (e : Expr) (q : ℚ) (z : ℝ) (hz : E q ∧ Value (x q) (y q) e z) :
    (inferQuotientDomain X Y D e).possible q := by
  cases e <;> simp only [inferQuotientDomain] <;> try exact hp q hz.1
  rename_i a b
  split
  · rename_i I J ha hb
    apply (quotientDomainRat_possible I J D q).mpr
    exact quotient_domain_possible (guarded_rational_sound hp hd he ha)
      (guarded_rational_sound hp hd he hb) ((quotient_relation a b q z).mpr hz)
  · exact hp q hz.1

/-- Definite membership supplies an actual value; crossing-zero numerical
uncertainty and failed child evaluation never count as absence or existence. -/
theorem inferQuotientDomain_definite {X Y : LinearInterval} {D : DomainBounds ℚ}
    {E : ℚ → Prop} {x y : ℚ → ℝ}
    (hp : ∀ q, E q → D.possible q) (hd : ∀ q, D.definite q → E q)
    (he : ∀ q, E q → (q:ℝ) ∈ Set.Icc (0:ℝ) 1 ∧
      X.Contains (q:ℝ) (x q) ∧ Y.Contains (q:ℝ) (y q))
    (e : Expr) (q : ℚ) (hq : (inferQuotientDomain X Y D e).definite q) :
    ∃ z, E q ∧ Value (x q) (y q) e z := by
  cases e <;> simp only [inferQuotientDomain] at hq <;> try exact hq.elim
  rename_i a b
  split at hq
  · rename_i I J ha hb
    obtain ⟨z, hz⟩ := quotient_domain_definite (guarded_rational_sound hp hd he ha)
      (guarded_rational_sound hp hd he hb) ((quotientDomainRat_definite I J D q).mp hq)
    exact ⟨z, (quotient_relation a b q z).mp hz⟩
  · exact hq.elim

end GeneralizedIntervalArithmetic
