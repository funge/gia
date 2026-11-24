import FinitePointDescriptions
import Mathlib.Data.Real.Irrational
import AuditPolicy
namespace GeneralizedIntervalArithmetic.FinitePointDescriptionsChecks
open FinitePointDescriptions

noncomputable def row : Code 1 := (Vector.ofFn (fun _ : Fin 1=>0),2)
noncomputable def one : Finset (Code 1) := {row}

theorem supplied_row_exact (p : Fin 1 → ℝ) (z : ℝ) :
    (p,z)∈table one ↔ p=(fun _=>0) ∧ z=2 := by
  simp [table,one,decode,row,Vector.get,Prod.mk.injEq]

theorem row_holes :
    ((fun _ : Fin 1=>(1:ℝ)),2)∉table one ∧
    ((fun _ : Fin 1=>(0:ℝ)),3)∉table one := by
  constructor
  · rw [supplied_row_exact]
    rintro ⟨he,_⟩
    have h := congrFun he 0
    norm_num at h
  · rw [supplied_row_exact]
    norm_num

theorem empty_table : table (∅ : Finset (Code 1)) = ∅ := by simp [table]

noncomputable def totalZero (_ : Fin 1 → ℝ) : Option ℝ := some 0

theorem finite_points_cannot_cover_total_zero :
    ¬ ∃ T : Finset (Code 1), table T = graph totalZero := by
  rw [function_representable_iff]
  rintro ⟨hf,_⟩
  have hd : domain totalZero = Set.univ := by ext p; simp [domain,totalZero]
  rw [hd] at hf
  exact Set.infinite_univ hf

/-- Finite support alone does not supply finite rational value descriptions. -/
theorem irrational_singleton_not_coded :
    ({((fun _ : Fin 1=>(0:ℝ)),Real.sqrt 2)} : Set ((Fin 1 → ℝ) × ℝ)).Finite ∧
    ¬ ∃ T : Finset (Code 1), table T = {((fun _=>0),Real.sqrt 2)} := by
  refine ⟨Set.finite_singleton _,?_⟩
  rw [representable_iff]
  rintro ⟨hf,hr⟩
  obtain ⟨c,hc⟩ := hr (Set.mem_singleton _)
  have he := congrArg Prod.snd hc
  exact irrational_sqrt_two ⟨c.2,he⟩

/-- A table can represent a multi-relation; being a partial function is extra. -/
theorem conflicting_rows_not_function :
    ¬ ∃ g : (Fin 1 → ℝ) → Option ℝ,
      table ({(Vector.ofFn (fun _ : Fin 1=>0),1),(Vector.ofFn (fun _ : Fin 1=>0),2)} : Finset (Code 1)) = graph g := by
  rintro ⟨g,he⟩
  have h1 : ((fun _ : Fin 1=>(0:ℝ)),1) ∈ graph g := by
    rw [← he]; simp [table,decode,Vector.get]
  have h2 : ((fun _ : Fin 1=>(0:ℝ)),2) ∈ graph g := by
    rw [← he]; simp [table,decode,Vector.get]
  have h : (some (1:ℝ)) = some 2 := h1.symm.trans h2
  norm_num at h

/-- An arbitrary semantic guard in one piece does not provide a finite code. -/
theorem arbitrary_domain_one_piece (A : Set (Fin 1 → ℝ)) (p : Fin 1 → ℝ) :
    IntervalSetDenotation.denote (fun _ : Unit=>arbitraryGuard A 0) {()} p =
      {z|p∈A ∧ z=0} := single_arbitrary_guard A 0 p

end GeneralizedIntervalArithmetic.FinitePointDescriptionsChecks
#audit_namespace GeneralizedIntervalArithmetic.FinitePointDescriptionsChecks
