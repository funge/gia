import IntervalSetExtension
import AuditPolicy
namespace GeneralizedIntervalArithmetic.IntervalSetExtensionChecks
open IntervalSetExtension IntervalSetDenotation GeneralFamilyDemotion

noncomputable def pieces (b : Bool) (_ : Unit) : Set ℝ :=
  if b then {1} else {0}

theorem two_pieces_exact : denote pieces Set.univ () = ({0,1} : Set ℝ) := by
  ext z
  simp [denote,pieces,Bool.exists_bool,or_comm]

/-- One finite exact set model is stricter than EVERY enclosing interval. -/
theorem two_pieces_strict : ∀ l u : EReal,
    denote pieces Set.univ () ⊆ ExtendedImageHull.interval l u →
    denote pieces Set.univ () ⊂ ExtendedImageHull.interval l u := by
  rw [two_pieces_exact]
  apply strict_against_every_interval ({0,1}:Set ℝ) (a:=0) (b:=1) (c:=1/2)
  all_goals norm_num

noncomputable def jump (x : ℝ) : ℝ := by
  classical
  exact if x < 0 then 0 else 1

theorem jump_image :
    outputs (fun (_ : Unit) (x : ℝ)=>x∈Set.Icc (-1:ℝ) 1)
      (fun _ x z=>z=jump x) () = ({0,1}:Set ℝ) := by
  classical
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    by_cases h : x<0 <;> simp [jump,h]
  · intro hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨-1,by norm_num,by norm_num [jump]⟩
    · exact ⟨1,by norm_num,by norm_num [jump]⟩

/-- A source-shaped bumpy witness against every constant closed interval model,
not against arbitrary parameter-dependent base families. -/
theorem jump_strict_every_constant_model : ∀ l u : EReal,
    (∀ x∈Set.Icc (-1:ℝ) 1, jump x∈ExtendedImageHull.interval l u) →
    denote pieces Set.univ () ⊂ ExtendedImageHull.interval l u := by
  intro l u h
  apply two_pieces_strict l u
  rw [two_pieces_exact,← jump_image]
  rintro z ⟨x,hx,rfl⟩
  exact h x hx

/-- Empty input pieces yield no outputs for positive arity, even for total G. -/
theorem empty_input :
    outputs (fun (_ : Unit) (x : Fin 1 → ℝ)=>∀ i,x i ∈ denote pieces ∅ ())
      (fun _ _ z=>z=7) () = ∅ := by
  ext z
  simp [outputs,IntervalSetDenotation.empty]

/-- Zero arity still admits the unique empty tuple: it is not a failed input. -/
theorem zero_arity :
    (7:ℝ) ∈ outputs (fun (_ : Unit) (_x : Fin 0 → ℝ)=>True)
      (fun _ _ z=>z=7) () := ⟨fun i=>Fin.elim0 i,trivial,rfl⟩

noncomputable def reciprocal (p : Fin 1 → ℝ) : Option ℝ := by
  classical
  exact if p 0 = 0 then none else some (1 / p 0)

theorem hole_preserved :
    denote (guardedPoint reciprocal)
      {q|q∈(Set.univ : Set (Fin 1 → ℝ)) ∧ ∃z,reciprocal q=some z} (fun _=>0) = ∅ := by
  rw [guarded_points_exact]
  ext z
  simp [reciprocal]

theorem defined_point :
    denote (guardedPoint reciprocal)
      {q|q∈(Set.univ : Set (Fin 1 → ℝ)) ∧ ∃z,reciprocal q=some z} (fun _=>2) = {1/2} := by
  rw [guarded_points_exact]
  ext z
  norm_num [reciprocal,eq_comm]

theorem outside_domain :
    denote (guardedPoint (fun _ : Fin 1 → ℝ=>some 7))
      {q|q∈({fun _=>0} : Set (Fin 1 → ℝ)) ∧ ∃z,(some (7:ℝ))=some z}
      (fun _=>1) = ∅ := by
  rw [guarded_points_exact]
  ext z
  simp only [Set.mem_setOf_eq,Set.mem_singleton_iff,Option.some.injEq,Set.mem_empty_iff_false,iff_false,not_and]
  intro h
  have he := congrFun h 0
  norm_num at he

theorem independent_relaxation_not_exact :
    (1:ℝ) ∈ outputs
      (fun (_ : Unit) (v : Fin 2 → ℝ)=>∀ i,v i∈Set.Icc (0:ℝ) 1)
      (fun _ v z=>z=v 0-v 1) () ∧
    (1:ℝ) ∉ outputs
      (fun (_ : Unit) (v : Fin 2 → ℝ)=>(∀ i,v i∈Set.Icc (0:ℝ) 1) ∧ v 0=v 1)
      (fun _ v z=>z=v 0-v 1) () := by
  constructor
  · refine ⟨![1,0],?_,by norm_num⟩
    intro i; fin_cases i <;> norm_num
  · rintro ⟨v,⟨hv,he⟩,hz⟩
    rw [he] at hz
    norm_num at hz

/-- A mere positive tolerance would produce a different, inexact representation. -/
theorem positive_tolerance_not_equality :
    (∑ i : Fin 1, ((fun _=> (0:ℝ)) i-(fun _=> (1/2:ℝ)) i)^2) ≤ 1 ∧
    (fun _ : Fin 1=>(0:ℝ)) ≠ (fun _ : Fin 1=>(1/2:ℝ)) := by
  norm_num
  intro h
  have he := congrFun h 0
  norm_num at he

end GeneralizedIntervalArithmetic.IntervalSetExtensionChecks
#audit_namespace GeneralizedIntervalArithmetic.IntervalSetExtensionChecks
