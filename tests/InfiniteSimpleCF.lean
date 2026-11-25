import InfiniteSimpleCF
import AuditPolicy
namespace GeneralizedIntervalArithmetic.InfiniteSimpleCFChecks
open InfiniteSimpleCF
open Filter
open scoped Topology

def ones (n : ℕ) : ℤ := if n=0 then 0 else 1

theorem ones_admissible : Admissible ones := by
  constructor
  · norm_num [ones]
  · intro n; simp [ones]

theorem ones_prefix : trunc ones 0 0=0 ∧ trunc ones 0 1=1 ∧
    trunc ones 0 2=1/2 ∧ trunc ones 0 3=2/3 ∧ trunc ones 0 4=3/5 := by
  norm_num [trunc,ones]

/-- Infinite tails may contain 1 forever; the finite last-term convention does
not impose a fictitious final coefficient on them. -/
theorem ones_recovered : ∃x:ℝ, 0<x ∧ (¬∃q:ℚ,x=(q:ℝ)) ∧
    GenContFract.of x=presentation ones ∧ Represents ones x :=
  admissible_reconstruction ones_admissible

theorem growing_admissible : Admissible (fun n => (n:ℤ)) := by
  constructor
  · norm_num
  · intro n; dsimp; omega

theorem unbounded_coefficients_allowed : ∃!x:ℝ, Represents (fun n => (n:ℤ)) x :=
  unique_value growing_admissible

theorem coefficient_recovery (a : ℕ→ℤ) (ha : Admissible a) (x : ℝ)
    (hx : Represents a x) : GenContFract.of x=presentation a :=
  (represents_iff ha x).1 hx

theorem stream_uniqueness (a b : ℕ→ℤ) (ha : Admissible a) (hb : Admissible b)
    (x : ℝ) (hx : Represents a x) (hy : Represents b x) : a=b :=
  (representation_unique ha hb hx hy).1 rfl

theorem zero_trunc (n k : ℕ) : trunc (fun _ => (0:ℤ)) n k=0 := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [trunc,ih]

theorem convergence_without_admissibility :
    SuffixLimits (fun _ => (0:ℤ)) (fun _ => (0:ℝ)) ∧
    ¬Admissible (fun _ => (0:ℤ)) ∧
    GenContFract.of (0:ℝ) ≠ presentation (fun _ => (0:ℤ)) := by
  refine ⟨?_,by simp [Admissible],?_⟩
  · intro n; simp [zero_trunc]
  · intro h
    have ht := (ContinuedFractionConversion.finite_iff_rational (0:ℝ)).2 ⟨0,by norm_num⟩
    rw [h] at ht
    exact presentation_infinite _ ht

theorem redundant_negative_outside_scope : ¬Admissible (fun _ => (-2:ℤ)) := by
  simp [Admissible]

theorem finite_prefix_bridge (n k : ℕ) :
    trunc ones n k=ContinuedFractionConversion.finiteValue (ones n)
      ((List.range k).map (fun j => (ones (n+j+1):ℚ))) := trunc_finite ones n k

theorem uniform_error (v : ℕ→ℝ) (hv : SuffixLimits ones v) :
    |v 0-(trunc ones 0 4:ℝ)|≤1/16 := by
  convert limit_error ones_admissible hv 0 2 using 1; norm_num

#eval (List.range 5).map (trunc ones 0)
end GeneralizedIntervalArithmetic.InfiniteSimpleCFChecks
#audit_namespace GeneralizedIntervalArithmetic.InfiniteSimpleCFChecks
