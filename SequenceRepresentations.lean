import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Normed

/-! Tupper §2.15.2: termwise rational arithmetic and its interpretation in ℝ. -/
namespace GeneralizedIntervalArithmetic.SequenceRepresentations
open Filter
open scoped Topology

def Represents (u : ℕ → ℚ) (x : ℝ) : Prop :=
  Tendsto (fun n => (u n : ℝ)) atTop (𝓝 x)

theorem unique {u : ℕ → ℚ} {x y : ℝ}
    (hx : Represents u x) (hy : Represents u y) : x=y := tendsto_nhds_unique hx hy

theorem constant (q : ℚ) : Represents (fun _ => q) q := tendsto_const_nhds

theorem add {u v : ℕ → ℚ} {x y : ℝ}
    (hu : Represents u x) (hv : Represents v y) :
    Represents (fun n => u n + v n) (x+y) := by
  simpa [Represents] using hu.add hv

theorem sub {u v : ℕ → ℚ} {x y : ℝ}
    (hu : Represents u x) (hv : Represents v y) :
    Represents (fun n => u n - v n) (x-y) := by
  simpa [Represents] using hu.sub hv

theorem mul {u v : ℕ → ℚ} {x y : ℝ}
    (hu : Represents u x) (hv : Represents v y) :
    Represents (fun n => u n * v n) (x*y) := by
  simpa [Represents] using hu.mul hv

/-- Division is an eventual partial operation: early zero entries are not
asserted defined, and the limiting denominator must be nonzero. -/
theorem div {u v : ℕ → ℚ} {x y : ℝ}
    (hu : Represents u x) (hv : Represents v y) (hy : y≠0) :
    (∀ᶠ n in atTop, v n ≠ 0) ∧ Represents (fun n => u n / v n) (x/y) := by
  constructor
  · have h := hv.eventually_ne hy
    filter_upwards [h] with n hn
    exact fun he => hn (by simp [he])
  · simpa [Represents] using hu.div hv hy

/-- Generic inheritance requires a continuous real operation and cast agreement.
This does not license arbitrary rational functions under the source's ⊕. -/
theorem lift_binary {u v : ℕ → ℚ} {x y : ℝ} (qop : ℚ → ℚ → ℚ)
    (op : ℝ × ℝ → ℝ) (hu : Represents u x) (hv : Represents v y)
    (hc : ContinuousAt op (x,y))
    (he : ∀a b:ℚ, (qop a b : ℝ) = op (a,b)) :
    Represents (fun n => qop (u n) (v n)) (op (x,y)) := by
  simpa [Represents,he] using hc.tendsto.comp (hu.prodMk_nhds hv)

theorem independent {u u' v v' : ℕ → ℚ} {x y z z' : ℝ}
    (qop : ℚ → ℚ → ℚ) (op : ℝ × ℝ → ℝ)
    (hu : Represents u x) (hu' : Represents u' x)
    (hv : Represents v y) (hv' : Represents v' y)
    (hc : ContinuousAt op (x,y))
    (he : ∀a b:ℚ, (qop a b : ℝ) = op (a,b))
    (hz : Represents (fun n=>qop (u n) (v n)) z)
    (hz' : Represents (fun n=>qop (u' n) (v' n)) z') : z=z' :=
  (unique hz (lift_binary qop op hu hv hc he)).trans
    (unique hz' (lift_binary qop op hu' hv' hc he)).symm

/-- A converging rational representative is the corresponding element of
mathlib's actual Cauchy quotient; convergence is not a new real-number axiom. -/
theorem construction {u : ℕ → ℚ} {x : ℝ} (h : Represents u x) :
    ∃hc : IsCauSeq abs u, Real.mk ⟨u,hc⟩ = x := by
  apply Real.of_near u x
  intro ε hε
  simpa [Real.dist_eq] using Metric.tendsto_atTop.mp h ε hε

/-- Exact reuse of mathlib's actual rational Cauchy quotient construction. -/
theorem quotient_operations (u v : CauSeq ℚ abs) :
    Real.mk (u+v) = Real.mk u + Real.mk v ∧
    Real.mk (u*v) = Real.mk u * Real.mk v ∧
    Real.mk (-u) = -Real.mk u := ⟨Real.mk_add,Real.mk_mul,Real.mk_neg⟩

theorem quotient_equality (u v : CauSeq ℚ abs) : Real.mk u = Real.mk v ↔ u≈v :=
  Real.mk_eq

end GeneralizedIntervalArithmetic.SequenceRepresentations
