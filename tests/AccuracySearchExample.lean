import AccuracySearchExample
import AuditPolicy
namespace GeneralizedIntervalArithmetic.AccuracySearchExampleChecks
open AccuracySearchExample ExpressionStreams

theorem rejected_prefix (n : ℕ) (hn : n < 2) :
    eval exactBackend (input n) (.point 0) nested = none := by
  change combine (some (.point 1))
    (eval exactBackend (input n) (.point 0) (.div .x (.const 2))) (guardedDiv exactBackend) = none
  cases he : eval exactBackend (input n) (.point 0) (.div .x (.const 2)) with
  | none => rfl
  | some J =>
    have hv : Value 0 0 (.div .x (.const 2)) 0 := by
      simpa using Value.div (Value.x (x:=0) (y:=0)) (Value.const 2) (by norm_num : (2:ℝ) ≠ 0)
    have hz := eval_sound exactBackend_sound
      (show (input n).Contains 0 by simp [input,hn,QInterval.Contains])
      (show (QInterval.point 0).Contains 0 by norm_num [QInterval.point,QInterval.Contains]) hv J he
    exact guardedDiv_zero_unknown exactBackend (.point 1) J
      ⟨by exact_mod_cast hz.1,by exact_mod_cast hz.2⟩

theorem chosen_stage_encloses_limit :
    ∃ I, eval exactBackend (input selected) (.point 0) nested = some I ∧ I.Contains 2 := by
  obtain ⟨I,he,hc,_⟩ := selected_certificate
  exact ⟨I,he,hc⟩
end GeneralizedIntervalArithmetic.AccuracySearchExampleChecks
#audit_namespace GeneralizedIntervalArithmetic.AccuracySearchExampleChecks
