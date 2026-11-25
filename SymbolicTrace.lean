import RootTransfer
import PartialRealArithmetic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Tupper §2.9.8, printed p.32: the concrete symbolic sine/root trace.
Set operations below act at one fixed parameter, not on independent projected
ranges. Square root and quotient retain their partial real domains. -/
namespace GeneralizedIntervalArithmetic.SymbolicTrace

/-- The existing guarded quotient graph lifted to sets of real values. -/
def quot (A B : Set ℝ) : Set ℝ :=
  {z | ∃ x ∈ A, ∃ y ∈ B, PartialRealArithmetic.divRel x y z}

theorem quot_singletons (x y z : ℝ) : z ∈ quot {x} {y} ↔ y≠0 ∧ z=x/y := by
  simp [quot]

theorem root_singleton (p z : ℝ) :
    z ∈ RootTransfer.roots {p} ↔ 0≤p ∧ z=Real.sqrt p := by
  simp [RootTransfer.roots,SqrtValues]

noncomputable def value (p : ℝ) : ℝ := p*Real.sin p + Real.sqrt p/(p+Real.pi)

/-- The unsimplified second line of the printed trace, at one shared p. -/
def trace (p : ℝ) : Set ℝ :=
  Set.image2 (·+·)
    (Set.image2 (·*·) {p} (Real.sin '' {p}))
    (quot (RootTransfer.roots {p}) (Set.image2 (·+·) {p} {Real.pi}))

theorem product_stage (p : ℝ) :
    Set.image2 (·*·) {p} (Real.sin '' {p}) = {p*Real.sin p} := by simp

theorem denominator_stage (p : ℝ) :
    Set.image2 (·+·) {p} {Real.pi} = {p+Real.pi} := by simp

theorem quotient_stage (p z : ℝ) :
    z ∈ quot (RootTransfer.roots {p}) (Set.image2 (·+·) {p} {Real.pi}) ↔
      0≤p ∧ p+Real.pi≠0 ∧ z=Real.sqrt p/(p+Real.pi) := by
  simp only [denominator_stage,quot,Set.mem_setOf_eq,Set.mem_singleton_iff,
    root_singleton,PartialRealArithmetic.divRel,PartialRealArithmetic.divDefined,
    PartialRealArithmetic.div]
  aesop

/-- Exact graph of the composition, including partiality outside [0,1]. -/
theorem trace_iff (p z : ℝ) : z ∈ trace p ↔ 0≤p ∧ z=value p := by
  have hp : 0≤p → p+Real.pi≠0 := fun h => ne_of_gt (add_pos_of_nonneg_of_pos h Real.pi_pos)
  simp only [trace,product_stage,Set.mem_image2,Set.mem_singleton_iff,quotient_stage]
  dsimp [value]
  constructor
  · rintro ⟨a,rfl,b,⟨h,_,rfl⟩,rfl⟩; exact ⟨h,rfl⟩
  · rintro ⟨h,rfl⟩
    exact ⟨_,rfl,_,⟨h,hp h,rfl⟩,rfl⟩

theorem defined_iff (p : ℝ) : (trace p).Nonempty ↔ 0≤p := by
  simp [Set.Nonempty,trace_iff]

theorem trace_exact {p : ℝ} (hp : 0≤p) : trace p = {value p} := by
  ext z; simp [trace_iff,hp]

theorem negative_absent {p : ℝ} (hp : p<0) : trace p = ∅ := by
  ext z; simp [trace_iff,not_le_of_gt hp]

noncomputable def bounds : FunctionalBounds ℝ := ⟨value,value⟩

theorem bounds_exact (p z : ℝ) : bounds.Contains p z ↔ z=value p := by
  change value p≤z ∧ z≤value p ↔ z=value p
  exact ⟨fun h => le_antisymm h.2 h.1,fun h => by rw [h]; exact ⟨le_rfl,le_rfl⟩⟩

/-- The final equal-bound pair agrees with the actual graph on the source domain. -/
theorem source_trace {p : ℝ} (hp : p∈Set.Icc (0:ℝ) 1) (z : ℝ) :
    z ∈ trace p ↔ bounds.Contains p z := by rw [bounds_exact,trace_iff]; simp [hp.1]

/-- Any sound pair contains this singleton; no computed global extremum follows. -/
theorem pointwise_least (B : FunctionalBounds ℝ) {p : ℝ} (hp : 0≤p)
    (h : ∀ z ∈ trace p, B.Contains p z) :
    B.lower p ≤ bounds.lower p ∧ bounds.upper p ≤ B.upper p :=
  h (value p) ((trace_iff p _).mpr ⟨hp,rfl⟩)

/-- External domains are intersected, never replaced by totalized sqrt/division. -/
theorem projection (D : Set ℝ) :
    {z | ∃ p ∈ D, z ∈ trace p} = value '' (D ∩ Set.Ici 0) := by
  ext z
  simp only [Set.mem_setOf_eq,trace_iff,Set.mem_image,Set.mem_inter_iff,Set.mem_Ici]
  aesop

/-- The source's projected range is exact, but is still an unevaluated image. -/
theorem source_projection :
    {z | ∃ p ∈ Set.Icc (0:ℝ) 1, z ∈ trace p} = value '' Set.Icc 0 1 := by
  rw [projection]
  ext z; simp only [Set.mem_image,Set.mem_inter_iff,Set.mem_Icc,Set.mem_Ici]
  aesop

/-- Exact domain flags for a chosen external parameter domain. The symbolic
payload is not itself a claim of definedness. -/
noncomputable def model (D : Set ℝ) : PartialEnclosure ℝ :=
  ⟨bounds,⟨fun p => p∈D ∧ 0≤p,fun p => p∈D ∧ 0≤p,fun _ h => h⟩⟩

theorem model_sound (D : Set ℝ) :
    (model D).Sound (fun p z => p∈D ∧ z∈trace p) := by
  refine ⟨?_,?_,?_⟩
  · intro p z h
    exact (bounds_exact p z).mpr ((trace_iff p z).mp h.2).2
  · intro p z h
    exact ⟨h.1,((trace_iff p z).mp h.2).1⟩
  · intro p h
    exact ⟨value p,h.1,(trace_iff p _).mpr ⟨h.2,rfl⟩⟩

end GeneralizedIntervalArithmetic.SymbolicTrace
