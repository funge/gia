import TrigHalving
import AuditPolicy

namespace GeneralizedIntervalArithmetic.TrigHalvingChecks
open HardwareAddition HardwareHalving

theorem division_failure : run (m := Id) (fun _ _ => none) (fun _ _ => none)
    (fun _ _ => none) (fun _ => some (⟨0,0⟩ : Bounds Nat))
    (fun _ => some ⟨1,1⟩) ⟨2,2⟩ ⟨1,1⟩ 3 ⟨1,1⟩ = none := rfl

theorem zero_depth : run (m := Id) (fun _ _ => none) (fun _ _ => none)
    (fun _ _ => none) (fun _ => some (⟨0,0⟩ : Bounds Nat))
    (fun _ => some ⟨1,1⟩) ⟨2,2⟩ ⟨1,1⟩ 0 ⟨0,0⟩ = some (⟨0,0⟩,⟨1,1⟩) := rfl

theorem refine_failure_retains_old : refine (m := Id)
    (fun _ => some (⟨1,3⟩ : Bounds Nat)) (fun _ => none)
    (fun a b => decide (a<b)) min max ⟨0,0⟩ = some ⟨1,3⟩ := rfl

theorem wider_refinement_retains_old : refine (m := Id)
    (fun _ => some (⟨1,3⟩ : Bounds Nat)) (fun _ => some ⟨0,4⟩)
    (fun a b => decide (a<b)) min max ⟨0,0⟩ = some ⟨1,3⟩ := rfl

theorem tighter_refinement : refine (m := Id)
    (fun _ => some (⟨1,4⟩ : Bounds Nat)) (fun _ => some ⟨2,3⟩)
    (fun a b => decide (a<b)) min max ⟨0,0⟩ = some ⟨2,3⟩ := rfl

/-- Exact identities, not an assumption that machine halving is exact. -/
theorem reconstruction (x : ℝ) :
    2*Real.sin (x/2)*Real.cos (x/2) = Real.sin x ∧
    2*(Real.cos (x/2))^2-1 = Real.cos x := by
  have h : 2*(x/2)=x := by ring
  constructor
  · rw [← Real.sin_two_mul,h]
  · rw [← Real.cos_two_mul,h]

end GeneralizedIntervalArithmetic.TrigHalvingChecks
#audit_namespace GeneralizedIntervalArithmetic.TrigHalvingChecks
