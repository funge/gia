import AffineConjunction
import AuditPolicy

namespace GeneralizedIntervalArithmetic.AffineConjunctionChecks
open AffineConjunction

def seed : LinearInterval := .exact ⟨-1,1⟩
def ordinary : QInterval := ⟨-1,1,by norm_num⟩
def candidate : LinearInterval := ⟨⟨1,-3⟩,⟨1,1⟩,by norm_num,by norm_num⟩
def kept : List LinearInterval := [.constant ordinary,candidate]
def twice : LinearInterval := .exact ⟨-2,2⟩

macro "compute_model" : tactic => `(tactic|
  norm_num [AffineUnary.square,AffineUnary.squareCandidate,AffineUnary.select,
    AffineUnary.propagate,AffineUnary.image,square,retain,seed,ordinary,candidate,kept,twice,
    LinearInterval.exact,LinearInterval.hull,LinearInterval.constant,LinearInterval.mul,
    LinearInterval.join,LinearInterval.add,QInterval.point,QInterval.mul,
    QAffine.productBounds,QAffine.productChord,QAffine.curvature,QAffine.add])

theorem candidate_result : AffineUnary.squareCandidate seed = some candidate := by compute_model

theorem candidate_hull : candidate.hull.lo = -3 ∧ candidate.hull.hi = 1 := by compute_model

theorem old_result : AffineUnary.square seed = some (.constant ordinary) := by compute_model

theorem kept_result : square seed = some kept := by compute_model

theorem twice_result : AffineUnary.image seed 2 0 = twice := by compute_model

theorem pointwise_not_wider {t z : ℝ} (hz : Contains kept t z) :
    (LinearInterval.constant ordinary).Contains t z :=
  contained_in_selected kept_result old_result hz

theorem composed_not_wider {t z : ℝ} (hz : Contains (add kept twice) t z) :
    ((LinearInterval.constant ordinary).add twice).Contains t z :=
  add_contained_in_selected kept_result old_result hz

theorem sound_composition {t x : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : seed.Contains t x) :
    Contains (add kept twice) t (x^2+2*x) := by
  simpa [twice_result] using square_add_image_sound kept_result 2 0 ht hx

theorem composed_lower_bound {t z : ℝ} (hz : Contains (add kept twice) t z) : -1 ≤ z := by
  have h := hz (candidate.add twice) (by simp [add,kept])
  have hl := h.1
  norm_num [candidate,twice,LinearInterval.add,LinearInterval.exact,QAffine.add,QAffine.value] at hl
  linarith

theorem target_excluded (t : ℝ) : ¬ ∃ z, Contains (add kept twice) t z ∧
    (-3/2 : ℝ) ≤ z ∧ z ≤ -5/4 := by
  rintro ⟨z,hz,_,hu⟩
  have h := composed_lower_bound hz
  linarith

theorem old_admits_target : ((LinearInterval.constant ordinary).add twice).Contains
    (1/4 : ℝ) (-3/2) := by
  norm_num [ordinary,twice,LinearInterval.constant,LinearInterval.exact,LinearInterval.add,
    LinearInterval.Contains,QAffine.add,QAffine.value]

theorem old_cannot_exclude : ¬ (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z : ℝ,
    -3/2 ≤ z ∧ z ≤ -5/4 → ¬ ((LinearInterval.constant ordinary).add twice).Contains t z) := by
  intro h
  exact h (1/4) (by norm_num) (-3/2) (by norm_num) old_admits_target

theorem ordinary_still_needed : (candidate.add twice).Contains (3/4 : ℝ) (-1/2) ∧
    ¬ Contains (add kept twice) (3/4 : ℝ) (-1/2) := by
  constructor
  · norm_num [candidate,twice,LinearInterval.add,LinearInterval.exact,LinearInterval.Contains,
      QAffine.add,QAffine.value]
  · intro h
    have ho := composed_not_wider h
    norm_num [ordinary,twice,LinearInterval.constant,LinearInterval.exact,LinearInterval.add,
      LinearInterval.Contains,QAffine.add,QAffine.value] at ho

def Input (t x : ℝ) := t ∈ Set.Icc (0:ℝ) 1 ∧ seed.Contains t x

theorem semantic_exclusion (t : ℝ) : ¬ ∃ z, SquareAffineValues Input 2 0 t z ∧
    (-3/2 : ℝ) ≤ z ∧ z ≤ -5/4 := by
  rintro ⟨z,hz,hl,hu⟩
  have he := relation_sound kept_result 2 0 (R := Input) (fun _ _ h => h) hz
  have hk : Contains (add kept twice) t z := by simpa [twice_result] using he
  exact target_excluded t ⟨z,hk,hl,hu⟩

/-- Old membership above does not mean the polynomial attains that value. -/
theorem actual_value_at_counterexample : SquareAffineValues Input 2 0 (1/4) (-3/4) := by
  refine ⟨-1/2, ⟨by norm_num, ?_⟩, by norm_num⟩
  norm_num [seed,LinearInterval.exact,LinearInterval.Contains,QAffine.value]

theorem hole_preserved : ¬ ∃ z, SquareAffineValues
    (fun t x => t ≠ 1/4 ∧ Input t x) 2 0 (1/4) z := by
  rw [domain_iff]
  simp

theorem ordinary_only : retain (some ordinary) none = some [.constant ordinary] := rfl
theorem affine_only : retain none (some candidate) = some [candidate] := rfl
theorem no_bounds : retain none none = none := rfl

theorem contradiction_retained : retain (some (.point 0)) (some (.constant (.point 1))) =
    some [.constant (.point 0), .constant (.point 1)] := rfl

theorem contradiction_not_fallback (t : ℝ) : ¬ ∃ z,
    Contains [.constant (.point 0), .constant (.point 1)] t z := by
  rintro ⟨z,hz⟩
  have h0 := (linear_constant_contains (.point 0) t z).mp (hz (.constant (.point 0)) (by simp))
  have h1 := (linear_constant_contains (.point 1) t z).mp (hz (.constant (.point 1)) (by simp))
  simp only [QInterval.Contains,QInterval.point] at h0 h1
  norm_num at h0 h1
  linarith

def uncertain : LinearInterval := ⟨⟨-1,0⟩,⟨0,1⟩,by norm_num,by norm_num⟩

theorem uncertain_all_witnesses : ∃ C, square uncertain = some C ∧
    ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x, uncertain.Contains t x →
      Contains (add C (AffineUnary.image uncertain (-2) 1)) t (x^2+((-2:ℝ)*x+1)) := by
  obtain ⟨C,hC⟩ := square_available uncertain
  refine ⟨C,hC,?_⟩
  intro t ht x hx
  simpa using square_add_image_sound hC (-2) 1 ht hx

-- Small exact, reproducible query comparison; not a timing experiment.
def ratValue (a : QAffine) (q : ℚ) : ℚ := (1-q)*a.atZero+q*a.atOne

theorem ratValue_cast (a : QAffine) (q : ℚ) :
    (ratValue a q : ℝ) = a.value (q : ℝ) := by
  simp [ratValue,QAffine.value]

def rejects (I : LinearInterval) (q : ℚ) : Bool :=
  decide (ratValue I.upper q < -3/2 ∨ -5/4 < ratValue I.lower q)

theorem rejects_sound {I : LinearInterval} {q : ℚ} (h : rejects I q = true)
    {z : ℝ} (hz : (-3/2:ℝ) ≤ z ∧ z ≤ -5/4) : ¬ I.Contains (q:ℝ) z := by
  have hh : ratValue I.upper q < -3/2 ∨ -5/4 < ratValue I.lower q := of_decide_eq_true h
  intro hi
  rcases hh with hu | hl
  · have hU : I.upper.value (q:ℝ) < (-3/2:ℝ) := by
      rw [← ratValue_cast]; exact_mod_cast hu
    linarith [hi.2,hz.1]
  · have hL : (-5/4:ℝ) < I.lower.value (q:ℝ) := by
      rw [← ratValue_cast]; exact_mod_cast hl
    linarith [hi.1,hz.2]

theorem any_rejects_sound {C : List LinearInterval} {q : ℚ}
    (h : C.any (fun I => rejects I q) = true) {z : ℝ}
    (hz : (-3/2:ℝ) ≤ z ∧ z ≤ -5/4) : ¬ Contains C (q:ℝ) z := by
  obtain ⟨I,hI,hi⟩ := List.any_eq_true.mp h
  intro hc
  exact rejects_sound hi hz (hc I hI)

def grid : List ℚ := [0,1/4,1/2,3/4,1]

theorem exact_query_counts :
    (grid.filter (rejects ((LinearInterval.constant ordinary).add twice))).length = 3 ∧
    (grid.filter (fun q => (add kept twice).any (fun I => rejects I q))).length = 5 := by
  norm_num [grid,rejects,ratValue,add,kept,candidate,ordinary,twice,LinearInterval.constant,
    LinearInterval.add,LinearInterval.exact,QAffine.add]

#audit_namespace GeneralizedIntervalArithmetic.AffineConjunctionChecks
end GeneralizedIntervalArithmetic.AffineConjunctionChecks
