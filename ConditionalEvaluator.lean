import PiecewiseSelection

namespace GeneralizedIntervalArithmetic

/-- A bounded conditional tree: guards and leaves use the existing arithmetic
language. Conditional expressions inside arithmetic/guards are not added here. -/
inductive ConditionalExpr where
  | leaf : Expr → ConditionalExpr
  | iteLt : Expr → ℚ → ConditionalExpr → ConditionalExpr → ConditionalExpr

/-- The guard must have a defined value. Only the active branch needs a value;
equality selects the false branch. No value is assigned to an undefined guard. -/
inductive ConditionalValue (x y : ℝ) : ConditionalExpr → ℝ → Prop where
  | leaf {e z} : Value x y e z → ConditionalValue x y (.leaf e) z
  | yes {g : Expr} {q : ℚ} {a b : ConditionalExpr} {u z : ℝ} : Value x y g u → u < (q:ℝ) → ConditionalValue x y a z →
      ConditionalValue x y (.iteLt g q a b) z
  | no {g : Expr} {q : ℚ} {a b : ConditionalExpr} {u z : ℝ} : Value x y g u → (q:ℝ) ≤ u → ConditionalValue x y b z →
      ConditionalValue x y (.iteLt g q a b) z

/-- Certified choices recurse only into the active branch. Unknown choices need
both branch enclosures; any missing guard/required-branch enclosure yields none. -/
def evalConditional (X Y : LinearInterval) : ConditionalExpr → Option LinearInterval
  | .leaf e => evalGuarded X Y e
  | .iteLt g q a b =>
    match evalGuarded X Y g with
    | none => none
    | some G => match decideLinearLt G q with
      | .yes => evalConditional X Y a
      | .no => evalConditional X Y b
      | .unknown => combineLinear (evalConditional X Y a) (evalConditional X Y b) LinearInterval.join

theorem evalConditional_leaf (X Y : LinearInterval) (e : Expr) :
    evalConditional X Y (.leaf e) = evalGuarded X Y e := rfl

theorem conditional_leaf_iff {x y z : ℝ} {e : Expr} :
    ConditionalValue x y (.leaf e) z ↔ Value x y e z := by
  constructor
  · intro h
    cases h with | leaf hv => exact hv
  · exact ConditionalValue.leaf

theorem decision_yes_lt {G : LinearInterval} {q : ℚ} {t u : ℝ}
    (hc : decideLinearLt G q = .yes) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hu : G.Contains t u) : u < (q:ℝ) := by
  unfold decideLinearLt at hc
  split at hc
  · rename_i h
    exact (linear_hull_encloses ht hu).2.trans_lt (by exact_mod_cast h)
  · split at hc <;> cases hc

theorem decision_no_le {G : LinearInterval} {q : ℚ} {t u : ℝ}
    (hc : decideLinearLt G q = .no) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hu : G.Contains t u) : (q:ℝ) ≤ u := by
  unfold decideLinearLt at hc
  split at hc
  · cases hc
  · split at hc
    · rename_i h
      exact (by exact_mod_cast h : (q:ℝ) ≤ G.hull.lo).trans (linear_hull_encloses ht hu).1
    · cases hc

private theorem join_some {a b : Option LinearInterval} {R : LinearInterval}
    (h : combineLinear a b LinearInterval.join = some R) :
    ∃ I J, a = some I ∧ b = some J ∧ I.join J = R := by
  cases a with
  | none => simp [combineLinear] at h
  | some I =>
    cases b with
    | none => simp [combineLinear] at h
    | some J => exact ⟨I,J,rfl,rfl,Option.some.inj h⟩

theorem evalConditional_sound {X Y R : LinearInterval} {t x y z : ℝ} {e : ConditionalExpr}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hv : ConditionalValue x y e z) (hr : evalConditional X Y e = some R) : R.Contains t z := by
  induction hv generalizing R with
  | leaf hv => exact evalGuarded_sound ht hx hy hv hr
  | @yes g q a b u z hg hlt ha ih =>
    simp only [evalConditional] at hr
    cases he : evalGuarded X Y g with
    | none => simp [he] at hr
    | some G =>
      have hu := evalGuarded_sound ht hx hy hg he
      simp only [he] at hr
      cases hc : decideLinearLt G q with
      | yes => exact ih (by simpa [hc] using hr)
      | no => exact (not_lt_of_ge (decision_no_le hc ht hu) hlt).elim
      | unknown =>
        obtain ⟨I,J,hi,hj,rfl⟩ := join_some (by simpa [hc] using hr)
        exact linear_join_left ht (ih hi)
  | @no g q a b u z hg hle hb ih =>
    simp only [evalConditional] at hr
    cases he : evalGuarded X Y g with
    | none => simp [he] at hr
    | some G =>
      have hu := evalGuarded_sound ht hx hy hg he
      simp only [he] at hr
      cases hc : decideLinearLt G q with
      | yes => exact (not_lt_of_ge hle (decision_yes_lt hc ht hu)).elim
      | no => exact ih (by simpa [hc] using hr)
      | unknown =>
        obtain ⟨I,J,hi,hj,rfl⟩ := join_some (by simpa [hc] using hr)
        exact linear_join_right ht (ih hj)

theorem evalConditional_defined {X Y R : LinearInterval} {t x y : ℝ} {e : ConditionalExpr}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hr : evalConditional X Y e = some R) : ∃ z, ConditionalValue x y e z := by
  induction e generalizing R with
  | leaf e =>
    obtain ⟨z,hz⟩ := evalGuarded_defined ht hx hy hr
    exact ⟨z,ConditionalValue.leaf hz⟩
  | iteLt g q a b iha ihb =>
    simp only [evalConditional] at hr
    cases he : evalGuarded X Y g with
    | none => simp [he] at hr
    | some G =>
      obtain ⟨u,hu⟩ := evalGuarded_defined ht hx hy he
      have hG := evalGuarded_sound ht hx hy hu he
      simp only [he] at hr
      cases hc : decideLinearLt G q with
      | yes =>
        obtain ⟨z,hz⟩ := iha (by simpa [hc] using hr)
        exact ⟨z,ConditionalValue.yes hu (decision_yes_lt hc ht hG) hz⟩
      | no =>
        obtain ⟨z,hz⟩ := ihb (by simpa [hc] using hr)
        exact ⟨z,ConditionalValue.no hu (decision_no_le hc ht hG) hz⟩
      | unknown =>
        obtain ⟨I,J,hi,hj,_⟩ := join_some (by simpa [hc] using hr)
        rcases lt_or_ge u (q:ℝ) with hlt | hle
        · obtain ⟨z,hz⟩ := iha hi
          exact ⟨z,ConditionalValue.yes hu hlt hz⟩
        · obtain ⟨z,hz⟩ := ihb hj
          exact ⟨z,ConditionalValue.no hu hle hz⟩

/-- Exact inactive-branch independence at the definitional evaluator level. -/
theorem evalConditional_known_yes {X Y G : LinearInterval} {g : Expr} {q : ℚ}
    (hg : evalGuarded X Y g = some G) (hc : decideLinearLt G q = .yes)
    (a b : ConditionalExpr) : evalConditional X Y (.iteLt g q a b) = evalConditional X Y a := by
  simp [evalConditional,hg,hc]

theorem evalConditional_known_no {X Y G : LinearInterval} {g : Expr} {q : ℚ}
    (hg : evalGuarded X Y g = some G) (hc : decideLinearLt G q = .no)
    (a b : ConditionalExpr) : evalConditional X Y (.iteLt g q a b) = evalConditional X Y b := by
  simp [evalConditional,hg,hc]

def ConditionalExpressionValues (A B : ℝ → ℝ → Prop) (e : ConditionalExpr) (t z : ℝ) : Prop :=
  ∃ x y, A t x ∧ B t y ∧ ConditionalValue x y e z

theorem evalConditional_relational_sound {X Y R : LinearInterval} {D E : DomainBounds ℝ}
    {A B : ℝ → ℝ → Prop} {e : ConditionalExpr}
    (hX : (X.onDomain D).Sound A) (hY : (Y.onDomain E).Sound B)
    (hr : evalConditional X Y e = some R) :
    (R.onDomain (D.inter E)).Sound (ConditionalExpressionValues A B e) := by
  refine ⟨?_,?_,?_⟩
  · rintro t z ⟨x,y,hx,hy,hv⟩
    exact evalConditional_sound (hX.2.1 t x hx).1 (hX.1 t x hx) (hY.1 t y hy) hv hr
  · rintro t z ⟨x,y,hx,hy,_⟩
    exact ⟨(hX.2.1 t x hx).1,(hX.2.1 t x hx).2,(hY.2.1 t y hy).2⟩
  · intro t ht
    obtain ⟨x,hx⟩ := hX.2.2 t ⟨ht.1,ht.2.1⟩
    obtain ⟨y,hy⟩ := hY.2.2 t ⟨ht.1,ht.2.2⟩
    obtain ⟨z,hz⟩ := evalConditional_defined ht.1 (hX.1 t x hx) (hY.1 t y hy) hr
    exact ⟨z,x,y,hx,hy,hz⟩

end GeneralizedIntervalArithmetic
