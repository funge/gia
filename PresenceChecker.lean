import ExpressionContinuity

namespace GeneralizedIntervalArithmetic

def inBox (X Y : QInterval) (a : ℚ × ℚ) : Prop :=
  X.lo ≤ a.1 ∧ a.1 ≤ X.hi ∧ Y.lo ≤ a.2 ∧ a.2 ≤ Y.hi

instance (X Y : QInterval) (a : ℚ × ℚ) : Decidable (inBox X Y a) :=
  inferInstanceAs (Decidable (X.lo ≤ a.1 ∧ a.1 ≤ X.hi ∧ Y.lo ≤ a.2 ∧ a.2 ≤ Y.hi))

theorem inBox_sound {X Y : QInterval} {a : ℚ × ℚ} (h : inBox X Y a) :
    X.Contains a.1 ∧ Y.Contains a.2 := by
  rcases h with ⟨h1, h2, h3, h4⟩
  exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩,
    ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩⟩

/-- Check a supplied segment, not a root search. Both sign orientations and
endpoint zeros are accepted. Every failed guard returns false (uncertified). -/
def certifySegment (B : Backend) (X Y : QInterval) (e : Expr) (a b : ℚ × ℚ) : Bool :=
  if inBox X Y a ∧ inBox X Y b then
    match eval B X Y e with
    | none => false
    | some _ =>
      match eval B (.point a.1) (.point a.2) e, eval B (.point b.1) (.point b.2) e with
      | some L, some U => decide ((L.hi ≤ 0 ∧ 0 ≤ U.lo) ∨ (U.hi ≤ 0 ∧ 0 ≤ L.lo))
      | _, _ => false
  else false

theorem certifySegment_sound {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {e : Expr} {a b : ℚ × ℚ}
    (hc : certifySegment B X Y e a b = true) :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y e 0 := by
  unfold certifySegment at hc
  split at hc
  · rename_i hin
    cases hR : eval B X Y e with
    | none => simp [hR] at hc
    | some R =>
      cases hL : eval B (.point a.1) (.point a.2) e with
      | none => simp [hR, hL] at hc
      | some L =>
        cases hU : eval B (.point b.1) (.point b.2) e with
        | none => simp [hR, hL, hU] at hc
        | some U =>
          simp only [hR, hL, hU] at hc
          have hs : (L.hi ≤ 0 ∧ 0 ≤ U.lo) ∨ (U.hi ≤ 0 ∧ 0 ≤ L.lo) :=
            of_decide_eq_true hc
          obtain ⟨hax, hay⟩ := inBox_sound hin.1
          obtain ⟨hbx, hby⟩ := inBox_sound hin.2
          rcases hs with hs | hs
          · exact evaluator_segment_presence hB hax hay hbx hby hR hL hU hs.1 hs.2
          · exact evaluator_segment_presence hB hbx hby hax hay hR hU hL hs.1 hs.2
  · simp at hc

inductive BoxResult where
  | empty | present | unknown
  deriving DecidableEq, Repr

def classifyWithSegment (B : Backend) (X Y : QInterval) (e : Expr)
    (a b : ℚ × ℚ) : BoxResult :=
  if classifyExpr B X Y e = .empty then .empty
  else if certifySegment B X Y e a b then .present else .unknown

theorem classifyWithSegment_empty {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {e : Expr} {a b : ℚ × ℚ}
    (hc : classifyWithSegment B X Y e a b = .empty) :
    ¬ ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y e 0 := by
  unfold classifyWithSegment at hc
  split at hc
  · rename_i h
    exact eval_empty_pixel hB h
  · split at hc <;> cases hc

theorem classifyWithSegment_present {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {e : Expr} {a b : ℚ × ℚ}
    (hc : classifyWithSegment B X Y e a b = .present) :
    ∃ x y, X.Contains x ∧ Y.Contains y ∧ Value x y e 0 := by
  unfold classifyWithSegment at hc
  split at hc
  · cases hc
  · split at hc
    · rename_i h
      exact certifySegment_sound hB h
    · cases hc

/-- Sound zero exclusion and sound presence certificates cannot disagree. -/
theorem empty_disallows_presence {B : Backend} (hB : BackendSound B)
    {X Y : QInterval} {e : Expr} {a b : ℚ × ℚ}
    (he : classifyExpr B X Y e = .empty) : certifySegment B X Y e a b = false := by
  cases hc : certifySegment B X Y e a b with
  | false => rfl
  | true => exact False.elim ((eval_empty_pixel hB he) (certifySegment_sound hB hc))

end GeneralizedIntervalArithmetic
