import FiniteGuardPieces
import AuditPolicy
namespace GeneralizedIntervalArithmetic.FiniteGuardPiecesChecks
open FiniteGuardPieces

def constant (q : ℚ) : QAffine := ⟨q,q⟩
def identity : QAffine := ⟨0,1⟩
def reverse : QAffine := ⟨1,0⟩
def interval (l u : ℚ) (ls us : Bool) : Description := band [] (constant l) (constant u) ls us

theorem interval_exact (l u : ℚ) (ls us : Bool) (t z : ℝ) :
    z ∈ (interval l u ls us).denote t ↔
      (if ls then (l:ℝ)<z else (l:ℝ)≤z) ∧ (if us then z<(u:ℝ) else z≤(u:ℝ)) := by
  have hc (q : ℚ) : (constant q).value t = (q:ℝ) := by simp [constant,QAffine.value]; ring
  rw [← compile_exact]
  simp [interval,band_exact,guardHolds,hc]

def closedTouch : Description := .inter (interval 0 1 false false) (interval 1 2 false false)
def openTouch : Description := .inter (interval 0 1 false false) (interval 1 2 true false)

theorem closed_touch (t : ℝ) : pieces closedTouch.compile t = {1} := by
  rw [compile_exact]
  ext z
  simp [closedTouch,Description.denote,interval_exact]
  constructor <;> intro h
  · linarith [h.1.2,h.2.1]
  · subst z; norm_num

theorem open_touch (t : ℝ) : pieces openTouch.compile t = ∅ := by
  rw [compile_exact]
  ext z
  simp [openTouch,Description.denote,interval_exact]
  intro _ hz hzz
  linarith

theorem reversed_empty (t : ℝ) : (interval 1 0 false false).denote t = ∅ := by
  ext z
  simp [interval_exact]
  intro h; linarith

theorem zero_width_open_empty (t : ℝ) : (interval 0 0 true false).denote t = ∅ := by
  ext z
  simp [interval_exact]

/-- Domain split at 1/2: the left piece owns the boundary, the right does not. -/
def split : Description := .union
  (band [(⟨-1/2,1/2⟩,false)] (constant 0) (constant 0) false false)
  (band [(⟨1/2,-1/2⟩,true)] (constant 2) (constant 2) false false)

theorem split_boundary_left : test split.compile (1/2) 0 = true := by norm_num [test, Description.compile, meet, band, guardAtoms, lower, upper, Atom.test, constant, interval, identity, reverse, split]
theorem split_boundary_not_right : test split.compile (1/2) 2 = false := by norm_num [test, Description.compile, meet, band, guardAtoms, lower, upper, Atom.test, constant, interval, identity, reverse, split]
theorem split_right : test split.compile (3/4) 2 = true := by norm_num [test, Description.compile, meet, band, guardAtoms, lower, upper, Atom.test, constant, interval, identity, reverse, split]
theorem split_left : test split.compile (1/4) 0 = true := by norm_num [test, Description.compile, meet, band, guardAtoms, lower, upper, Atom.test, constant, interval, identity, reverse, split]
theorem split_gap : test split.compile (3/4) 1 = false := by norm_num [test, Description.compile, meet, band, guardAtoms, lower, upper, Atom.test, constant, interval, identity, reverse, split]

def diagonal := band [] identity identity false false
def antidiagonal := band [] reverse reverse false false

theorem shared_intersection_rejects : test (Description.inter diagonal antidiagonal).compile 0 0 = false := by norm_num [test, Description.compile, meet, band, guardAtoms, lower, upper, Atom.test, constant, interval, identity, reverse, split, diagonal, antidiagonal, closedTouch, openTouch]
theorem shared_intersection_midpoint : test (Description.inter diagonal antidiagonal).compile (1/2) (1/2) = true := by norm_num [test, Description.compile, meet, band, guardAtoms, lower, upper, Atom.test, constant, interval, identity, reverse, split, diagonal, antidiagonal, closedTouch, openTouch]

/-- Projecting away the parameter before intersection would admit zero using
 two different parameters; the same-parameter compiled intersection rejects it. -/
theorem correlation_control :
    (∃ t : ℝ, (0:ℝ) ∈ diagonal.denote t) ∧
    (∃ t : ℝ, (0:ℝ) ∈ antidiagonal.denote t) ∧
    (0:ℝ) ∉ (Description.inter diagonal antidiagonal : Description).denote 0 := by
  refine ⟨⟨0,?_⟩,⟨1,?_⟩,?_⟩
  · simpa using (compiled_test_exact diagonal 0 0).mp (by norm_num [test, Description.compile, meet, band, guardAtoms, lower, upper, Atom.test, constant, interval, identity, reverse, split, diagonal, antidiagonal, closedTouch, openTouch])
  · simpa using (compiled_test_exact antidiagonal 1 0).mp (by norm_num [test, Description.compile, meet, band, guardAtoms, lower, upper, Atom.test, constant, interval, identity, reverse, split, diagonal, antidiagonal, closedTouch, openTouch])
  · intro h
    have hh := (compiled_test_exact (Description.inter diagonal antidiagonal) 0 0).mpr (by simpa using h)
    rw [shared_intersection_rejects] at hh
    contradiction

theorem empty_not_unconstrained : test Description.empty.compile 0 0 = false ∧
    test (Description.cell []).compile 0 0 = true := by norm_num [test, Description.compile, meet, band, guardAtoms, lower, upper, Atom.test, constant, interval, identity, reverse, split, diagonal, antidiagonal, closedTouch, openTouch]

theorem distributed_boundary : test (Description.inter (Description.union closedTouch split) openTouch).compile (1/2) 1 = false := by norm_num [test, Description.compile, meet, band, guardAtoms, lower, upper, Atom.test, constant, interval, identity, reverse, split, diagonal, antidiagonal, closedTouch, openTouch]

end GeneralizedIntervalArithmetic.FiniteGuardPiecesChecks
#audit_namespace GeneralizedIntervalArithmetic.FiniteGuardPiecesChecks
