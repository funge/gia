import MixedEndpoints
import AuditPolicy
namespace GeneralizedIntervalArithmetic.MixedEndpointsChecks
open MixedEndpoints FiniteGuardPieces

def mixed : Band := ⟨0,1/2,3/2,-1,true,false,[]⟩
def closedMixed : Band := {mixed with lowerOpen := false}
def constant (n : ℤ) : Band := ⟨n,0,n,0,false,false,[]⟩
def guarded : Band := {constant 0 with guards := [(⟨0,1⟩,true)]}

macro "checkCode" : tactic => `(tactic| norm_num [test,Description.compile,band,
  guardAtoms,lower,upper,Atom.test,Band.encode,Band.lower,Band.upper,
  QAffine.ofCoefficients,mixed,closedMixed,constant,guarded])

theorem open_tip_excluded : test mixed.encode.compile 0 0 = false := by checkCode
theorem closed_tip_included : test mixed.encode.compile 0 (3/2) = true := by checkCode
theorem interior_included : test mixed.encode.compile (1/2) (1/2) = true := by checkCode
theorem equal_open_excluded : test mixed.encode.compile 1 (1/2) = false := by checkCode
theorem closing_changes_boundary : test closedMixed.encode.compile 1 (1/2) = true := by checkCode
theorem guard_boundary_excluded : test guarded.encode.compile 0 0 = false := by checkCode
theorem guard_interior_included : test guarded.encode.compile (-1) 0 = true := by checkCode

theorem exact_nonempty (t : ℝ) : (pieces mixed.encode.compile t).Nonempty ↔ t<1 := by
  rw [fiber_nonempty]
  norm_num [mixed,Band.lowerValue,Band.upperValue,guardHolds]
  constructor <;> intro h <;> linarith

theorem equal_open_empty : pieces mixed.encode.compile 1 = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rw [exact_nonempty]
  norm_num

theorem reversed_empty : pieces mixed.encode.compile 2 = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rw [exact_nonempty]
  norm_num

theorem guard_empty : pieces guarded.encode.compile 0 = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rw [fiber_nonempty]
  norm_num [guarded,constant,guardHolds,QAffine.value]

theorem constant_denotation (n : ℤ) (t : ℝ) :
    (constant n).denote t = {(n:ℝ)} := by
  ext z
  simp [Band.denote,constant,guardHolds,Band.lowerValue,Band.upperValue,
    ← le_antisymm_iff,eq_comm]

def choices : Set Band := {constant 0,constant 1}

/-- Independently selecting a band at each use can admit the identity's
samples; this is not a single persistent choice. -/
theorem marginal_samples : ∀ t ∈ ({0,1} : Set ℝ),
    t ∈ IntervalSetDenotation.denote Band.denote choices t := by
  intro t ht
  rcases ht with ht | ht
  · subst t
    refine ⟨constant 0,by simp [choices],?_⟩
    rw [constant_denotation]; simp
  · have ht' : t=1 := ht
    subst t
    refine ⟨constant 1,by simp [choices],?_⟩
    rw [constant_denotation]; simp

theorem no_source_joint : ¬ ∃ b ∈ choices, ∀ t ∈ ({0,1} : Set ℝ),
    t ∈ b.denote t := by
  rintro ⟨b,hb,h⟩
  simp only [choices,Set.mem_insert_iff,Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl
  · have h1 := h 1 (by simp)
    rw [constant_denotation] at h1
    norm_num at h1
  · have h0 := h 0 (by simp)
    rw [constant_denotation] at h0
    norm_num at h0

theorem no_target_joint : ¬ ∃ d ∈ Band.encode '' choices,
    ∀ t ∈ ({0,1} : Set ℝ), t ∈ pieces d.compile t := by
  rw [← joint_exact]
  exact no_source_joint

theorem witness_bridge (T : Set ℝ) :
    CoefficientWitnesses.realizes
      (CoefficientWitnesses.decodePairs (fun p : ℤ => (p:ℝ)) (fun q : ℚ => (q:ℝ)) {(0,1/2)})
      T mixed.lowerValue := (endpoint_witnesses mixed T).1

end GeneralizedIntervalArithmetic.MixedEndpointsChecks
#audit_namespace GeneralizedIntervalArithmetic.MixedEndpointsChecks
