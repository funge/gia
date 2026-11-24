import FiniteProperties
import AuditPolicy

namespace GeneralizedIntervalArithmetic.FinitePropertiesChecks
open PartialProperties FiniteProperties Filter
open scoped Topology

def repeated (i : Fin 2) : PartialReal := fun x => some (x + (i:ℕ))
def plus (v : Fin 2 → ℝ) : Option ℝ := some (v 0 + v 1)

theorem two_actual_inputs (x : ℝ) : composeN plus repeated x = some (x+(x+1)) := by
  apply (composeN_some _ _ _ _).mpr
  refine ⟨fun i => x + (i:ℕ),fun _ => rfl,?_⟩
  simp [plus]

theorem continuous_two_input : ContinuousOnPartial (composeN plus repeated) Set.univ := by
  apply continuous_composeN (T := Set.univ)
  · intro i
    exact ⟨fun x => x+(i:ℕ),(continuous_id.add continuous_const).continuousOn,fun _ _ => rfl⟩
  · exact ⟨fun v => v 0 + v 1,((continuous_apply 0).add (continuous_apply 1)).continuousOn,
      fun _ _ => rfl⟩
  · exact fun _ _ _ _ => Set.mem_univ _

theorem absent_ignored_input :
    composeN (fun _ : Fin 2 → ℝ => some 7)
      (fun i _ => if i = 0 then none else some 2) 0 = none := by
  apply missing_input (i := 0)
  simp

theorem nullary_defined :
    composeN (fun _ : Fin 0 → ℝ => some 7) (fun i => Fin.elim0 i) 0 = some 7 := by
  apply (composeN_some _ _ _ _).mpr
  exact ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i,rfl⟩

theorem nullary_undefined :
    composeN (fun _ : Fin 0 → ℝ => none) (fun i => Fin.elim0 i) 0 = none := by
  cases h : composeN (fun _ : Fin 0 → ℝ => none) (fun i => Fin.elim0 i) 0 with
  | none => rfl
  | some z =>
    obtain ⟨v,_,hv⟩ := (composeN_some _ _ _ _).mp h
    contradiction

theorem local_constants_compose : LocallyConstantWithin
    (composeN plus (fun i _ => some (i:ℕ))) Set.univ 0 := by
  apply locally_constant_composeN
  · intro i
    exact ⟨(i:ℕ),rfl,Filter.Eventually.of_forall (fun _ => rfl)⟩
  · exact ⟨fun i => (i:ℕ),1,fun _ => rfl,by norm_num [plus]⟩

theorem empty_relative_set_does_not_supply_value :
    ¬ LocallyConstantWithin (fun _ => none) ∅ 0 := by
  rintro ⟨z,hz,_⟩
  contradiction

/-- The two children share x; projecting them independently would lose this. -/
theorem shared_input_cancel (x : ℝ) :
    composeN (fun v : Fin 2 → ℝ => some (v 0-v 1)) (fun _ t => some t) x = some 0 := by
  apply (composeN_some _ _ _ _).mpr
  exact ⟨fun _ => x,fun _ => rfl,by simp⟩

/-- Use the existing recursive AST and actual Value relation, not a new syntax. -/
theorem recursive_expression_control :
    ∀ᶠ _t in nhdsWithin (0:ℝ) Set.univ, Value (2:ℝ) (3:ℝ) (.add .x .y) 5 := by
  apply expr_locally_fixed (X := fun _ => 2) (Y := fun _ => 3) (.add .x .y)
  · exact_mod_cast (Value.add (x := (2:ℝ)) (y := (3:ℝ)) Value.x Value.y)
  · exact Filter.Eventually.of_forall (fun _ => rfl)
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end GeneralizedIntervalArithmetic.FinitePropertiesChecks
#audit_namespace GeneralizedIntervalArithmetic.FinitePropertiesChecks
