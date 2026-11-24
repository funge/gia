import IntervalSetExtension
import Mathlib.Data.Real.Irrational
import Mathlib.Order.Interval.Set.Infinite

/-! Finite *coded* point descriptions, distinct from arbitrary predicate guards. -/
namespace GeneralizedIntervalArithmetic.FinitePointDescriptions
open IntervalSetDenotation IntervalSetExtension
open scoped BigOperators

abbrev Code (n : ℕ) := Vector ℚ n × ℚ
noncomputable def decode {n} (c : Code n) : (Fin n → ℝ) × ℝ :=
  (fun i=>(c.1.get i:ℝ), (c.2:ℝ))

theorem decode_injective {n} : Function.Injective (@decode n) := by
  intro a b h
  apply Prod.ext
  · apply Vector.ext
    intro i hi
    have he := congrFun (congrArg Prod.fst h) ⟨i,hi⟩
    change (a.1[i]:ℝ) = (b.1[i]:ℝ) at he
    exact_mod_cast he
  · have he := congrArg Prod.snd h
    simp only [decode] at he
    exact_mod_cast he

noncomputable def point {n} (c : Code n) (p : Fin n → ℝ) : Set ℝ :=
  {z | (p,z)=decode c}
noncomputable def table {n} (T : Finset (Code n)) : Set ((Fin n → ℝ) × ℝ) :=
  decode '' (T : Set (Code n))

theorem table_denotation {n} (T : Finset (Code n)) (p : Fin n → ℝ) (z : ℝ) :
    (p,z)∈table T ↔ z∈denote point (T : Set (Code n)) p := by
  simp only [table,Set.mem_image,denote,Set.mem_setOf_eq,point]
  constructor <;> rintro ⟨c,hc,he⟩ <;> exact ⟨c,hc,he.symm⟩

/-- The finite row has precisely the source's polynomial zero-distance guard. -/
theorem point_guard {n} (c : Code n) (p : Fin n → ℝ) (z : ℝ) :
    z∈point c p ↔ (∑ i,(p i-(c.1.get i:ℝ))^2)≤0 ∧ z=(c.2:ℝ) := by
  simp [point,decode,Prod.mk.injEq,squared_guard_iff]

/-- Exact representability, not merely a finite list of arbitrary semantic sets. -/
theorem representable_iff {n} (G : Set ((Fin n → ℝ) × ℝ)) :
    (∃ T : Finset (Code n), table T = G) ↔ G.Finite ∧ G ⊆ Set.range decode := by
  constructor
  · rintro ⟨T,rfl⟩
    exact ⟨T.finite_toSet.image decode,Set.image_subset_range _ _⟩
  · rintro ⟨hf,hr⟩
    classical
    have hp : (decode ⁻¹' G).Finite := hf.preimage decode_injective.injOn
    refine ⟨hp.toFinset,?_⟩
    rw [table,Set.Finite.coe_toFinset,Set.image_preimage_eq_of_subset hr]

theorem irrational_point_not_representable {n} (p : Fin n → ℝ) (r : ℝ)
    (hr : Irrational r) : ¬ ∃ T : Finset (Code n), table T = {(p,r)} := by
  rw [representable_iff]
  rintro ⟨hf,h⟩
  obtain ⟨c,hc⟩ := h (Set.mem_singleton _)
  exact hr ⟨c.2,congrArg Prod.snd hc⟩

/-- The domain of a partial function cannot be made finite just by naming it. -/
noncomputable def graph {P : Type*} (g : P → Option ℝ) : Set (P × ℝ) :=
  {pz | g pz.1 = some pz.2}
noncomputable def domain {P : Type*} (g : P → Option ℝ) : Set P := {p|∃z,g p=some z}

theorem graph_domain {P : Type*} (g : P → Option ℝ) :
    Prod.fst '' graph g = domain g := by
  ext p
  constructor
  · rintro ⟨⟨q,z⟩,hz,rfl⟩
    exact ⟨z,hz⟩
  · rintro ⟨z,hz⟩
    exact ⟨(p,z),hz,rfl⟩

theorem finite_graph_iff_domain {P : Type*} (g : P → Option ℝ) :
    (graph g).Finite ↔ (domain g).Finite := by
  constructor
  · intro h
    rw [← graph_domain]
    exact h.image Prod.fst
  · intro h
    apply Set.Finite.of_finite_image (f:=Prod.fst)
    · rw [graph_domain]; exact h
    · intro a ha b hb he
      apply Prod.ext he
      have hz : some a.2 = some b.2 := by
        rw [← ha,← hb,he]
      exact Option.some.inj hz

theorem function_representable_iff {n} (g : (Fin n → ℝ) → Option ℝ) :
    (∃ T : Finset (Code n), table T = graph g) ↔
      (domain g).Finite ∧ graph g ⊆ Set.range decode := by
  rw [representable_iff,finite_graph_iff_domain]

/-- Arbitrary guards can hide ANY domain in one piece. This is semantic
expressiveness only, not a finite syntactic description theorem. -/
def arbitraryGuard {P : Type*} (A : Set P) (r : ℝ) (p : P) : Set ℝ :=
  {z|p∈A ∧ z=r}

theorem single_arbitrary_guard {P : Type*} (A : Set P) (r : ℝ) (p : P) :
    denote (fun _ : Unit=>arbitraryGuard A r) {()} p = {z|p∈A ∧ z=r} := by
  rw [IntervalSetDenotation.singleton]
  rfl

end GeneralizedIntervalArithmetic.FinitePointDescriptions
