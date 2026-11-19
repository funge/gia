import HardwareEvaluator
import AuditPolicy

namespace GeneralizedIntervalArithmetic.HardwareEvaluatorChecks
open HardwareEvaluator HardwareAddition

-- Executable control cases use rationals as a test backend only.
def lt (a b : ℚ) : Bool := decide (a < b)

theorem intersection : merge lt min max (some (⟨0,1⟩ : Bounds ℚ)) (some ⟨0,1/4⟩) =
    .bound ⟨0,1/4⟩ := by norm_num [merge,HardwareQuadrants.clip,lt]

theorem ordinary_fallback : merge lt min max (some (⟨0,1⟩ : Bounds ℚ)) none =
    .bound ⟨0,1⟩ := rfl

theorem affine_fallback : merge lt min max none (some (⟨0,1/4⟩ : Bounds ℚ)) =
    .bound ⟨0,1/4⟩ := rfl

theorem both_fail : merge lt min max none none = .unknown := rfl

theorem contradiction_is_not_fallback :
    merge lt min max (some (⟨0,1⟩ : Bounds ℚ)) (some ⟨2,3⟩) = .conflict := by
  norm_num [merge,HardwareQuadrants.clip,lt]

theorem touching_is_not_conflict :
    merge lt min max (some (⟨0,1⟩ : Bounds ℚ)) (some ⟨1,2⟩) = .bound ⟨1,1⟩ := by
  norm_num [merge,HardwareQuadrants.clip,lt]

-- Full syntactic semantics -> both concrete representations -> intersection.
theorem integrated_enclosure {C F : Type} {cd : C → Option ℝ} {decode : F → Option ℝ}
    {kc : C → Option (Bounds F)} {ka : C → Option (HardwareAffine.Form F)}
    {I : Option (Bounds F)} {A : Option (HardwareAffine.Form F)}
    {add sub mul : Bounds F → Bounds F → Option (Bounds F)}
    {cmp : F → F → Bool} {mn mx : F → F → F} {B : Bounds F} {t x : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hb : ∀ u ∈ Set.Icc (0:ℝ) (1/4), Contains decode B u)
    (hkc : ∀ c O v, kc c = some O → cd c = some v → Contains decode O v)
    (hka : ∀ c O v, ka c = some O → cd c = some v → HardwareAffine.Contains decode O t v)
    (hI : ∀ O, I = some O → Contains decode O x)
    (hA : ∀ O, A = some O → HardwareAffine.Contains decode O t x)
    (hp : HardwareIntervalOps.OpSound decode add (· + ·))
    (hs : HardwareIntervalOps.OpSound decode sub (· - ·))
    (hm : HardwareIntervalOps.OpSound decode mul (· * ·))
    (hc : HardwareDivision.CompareSound decode cmp)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hx : HardwareMultiplication.SelectSound decode mx max)
    {e : Polynomial C} {v : ℝ} (he : Value cd x e v) {O : Bounds F}
    (hr : run (m := Id) (eval kc I add sub mul) (affineEval ka A add sub mul B) cmp mn mx e = .bound O) :
    Contains decode O v :=
  run_sound hc hn hx ht
    (fun _ h => ordinary_eval_sound hkc hI hp hs hm he h)
    (fun _ h => affine_eval_sound ht hb hka hA hp hs hm he h) hr

-- Applying the compositional theorem to ALL values in the input interval.
theorem whole_input_enclosure {C F : Type} {cd : C → Option ℝ} {decode : F → Option ℝ}
    {kc : C → Option (Bounds F)} {ka : C → Option (HardwareAffine.Form F)}
    {I : Bounds F} {add sub mul : Bounds F → Bounds F → Option (Bounds F)}
    {cmp : F → F → Bool} {mn mx : F → F → F} {B : Bounds F}
    (hb : ∀ u ∈ Set.Icc (0:ℝ) (1/4), Contains decode B u)
    (hkc : ∀ c O v, kc c = some O → cd c = some v → Contains decode O v)
    (hka : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ c O v, ka c = some O → cd c = some v → HardwareAffine.Contains decode O t v)
    (hp : HardwareIntervalOps.OpSound decode add (· + ·))
    (hs : HardwareIntervalOps.OpSound decode sub (· - ·))
    (hm : HardwareIntervalOps.OpSound decode mul (· * ·))
    (hc : HardwareDivision.CompareSound decode cmp)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hx : HardwareMultiplication.SelectSound decode mx max)
    {e : Polynomial C} {x v : ℝ} (hinput : Contains decode I x)
    (he : Value cd x e v) {O : Bounds F}
    (hr : run (m := Id) (eval kc (some I) add sub mul)
      (affineEval ka (some (seed I)) add sub mul B) cmp mn mx e = .bound O) :
    Contains decode O v := by
  obtain ⟨t,ht,hseed⟩ := seed_covers hinput
  exact integrated_enclosure ht hb hkc (hka t ht)
    (fun _ h => by cases h; exact hinput) (fun _ h => by cases h; exact hseed)
    hp hs hm hc hn hx he hr

-- A failed ordinary traversal does not prevent the second traversal running.
theorem second_track_survives_first_failure :
    run (m := Id) (C := ℚ) (fun _ => none)
      (fun _ => some (⟨⟨0,0⟩,⟨1,1⟩⟩ : HardwareAffine.Form ℚ))
      lt min max .var = .bound ⟨0,1⟩ := by
  norm_num [run,merge,HardwareAffine.hull]

#audit_namespace GeneralizedIntervalArithmetic.HardwareEvaluatorChecks
end GeneralizedIntervalArithmetic.HardwareEvaluatorChecks
