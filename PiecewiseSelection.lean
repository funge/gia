import GuardedEvaluator

namespace GeneralizedIntervalArithmetic

inductive BranchDecision | yes | no | unknown deriving DecidableEq, Repr

/-- A decision about a total predicate across the certified parameter range.
Unknown makes no truth claim and is not a statement of undefinedness. -/
def BranchSound (c : BranchDecision) (P : ℝ → Prop) : Prop :=
  match c with
  | .yes => ∀ t ∈ Set.Icc (0:ℝ) 1, P t
  | .no => ∀ t ∈ Set.Icc (0:ℝ) 1, ¬ P t
  | .unknown => True

/-- Strict comparison: equality belongs to the false branch. -/
def decideLinearLt (G : LinearInterval) (q : ℚ) : BranchDecision :=
  if G.hull.hi < q then .yes else if q ≤ G.hull.lo then .no else .unknown

theorem decideLinearLt_sound {G : LinearInterval} {g : ℝ → ℝ} (q : ℚ)
    (hg : ∀ t ∈ Set.Icc (0:ℝ) 1, G.Contains t (g t)) :
    BranchSound (decideLinearLt G q) (fun t => g t < q) := by
  unfold decideLinearLt
  split
  · rename_i h
    intro t ht
    exact (linear_hull_encloses ht (hg t ht)).2.trans_lt (by exact_mod_cast h)
  · split
    · rename_i h
      intro t ht
      exact not_lt_of_ge ((by exact_mod_cast h : (q:ℝ) ≤ G.hull.lo).trans
        (linear_hull_encloses ht (hg t ht)).1)
    · trivial

def selectLinear : BranchDecision → LinearInterval → LinearInterval → LinearInterval
  | .yes, I, _ => I
  | .no, _, J => J
  | .unknown, I, J => I.join J

/-- With an unresolved guard, both branches must be definitely defined to
certify existence, while either branch may supply a possible value. -/
def selectDomain {α : Type*} : BranchDecision → DomainBounds α → DomainBounds α → DomainBounds α
  | .yes, D, _ => D
  | .no, _, E => E
  | .unknown, D, E =>
    ⟨fun p => D.definite p ∧ E.definite p, fun p => D.possible p ∨ E.possible p,
     fun p h => Or.inl (D.consistent p h.1)⟩

def PiecewiseValues (P : ℝ → Prop) (A B : ℝ → ℝ → Prop) (t z : ℝ) : Prop :=
  (P t ∧ A t z) ∨ (¬ P t ∧ B t z)

/-- Active-branch semantics. No continuity or branch-domain intersection is
assumed for a known decision. The predicate itself is total, not a partial guard. -/
theorem select_domain_sound {c : BranchDecision} {P : ℝ → Prop}
    {I J : LinearInterval} {D E : DomainBounds ℝ} {A B : ℝ → ℝ → Prop}
    (hc : BranchSound c P) (hI : (I.onDomain D).Sound A) (hJ : (J.onDomain E).Sound B) :
    ((selectLinear c I J).onDomain (selectDomain c D E)).Sound (PiecewiseValues P A B) := by
  classical
  cases c with
  | yes =>
    refine ⟨?_,?_,?_⟩
    · rintro t z (⟨_,ha⟩ | ⟨hp,hb⟩)
      · exact hI.1 t z ha
      · exact (hp (hc t (hJ.2.1 t z hb).1)).elim
    · rintro t z (⟨_,ha⟩ | ⟨hp,hb⟩)
      · exact hI.2.1 t z ha
      · exact (hp (hc t (hJ.2.1 t z hb).1)).elim
    · intro t ht
      obtain ⟨z,hz⟩ := hI.2.2 t ht
      exact ⟨z,Or.inl ⟨hc t ht.1,hz⟩⟩
  | no =>
    refine ⟨?_,?_,?_⟩
    · rintro t z (⟨hp,ha⟩ | ⟨_,hb⟩)
      · exact (hc t (hI.2.1 t z ha).1 hp).elim
      · exact hJ.1 t z hb
    · rintro t z (⟨hp,ha⟩ | ⟨_,hb⟩)
      · exact (hc t (hI.2.1 t z ha).1 hp).elim
      · exact hJ.2.1 t z hb
    · intro t ht
      obtain ⟨z,hz⟩ := hJ.2.2 t ht
      exact ⟨z,Or.inr ⟨hc t ht.1,hz⟩⟩
  | unknown =>
    refine ⟨?_,?_,?_⟩
    · rintro t z (⟨_,ha⟩ | ⟨_,hb⟩)
      · exact linear_join_left (hI.2.1 t z ha).1 (hI.1 t z ha)
      · exact linear_join_right (hJ.2.1 t z hb).1 (hJ.1 t z hb)
    · rintro t z (⟨_,ha⟩ | ⟨_,hb⟩)
      · exact ⟨(hI.2.1 t z ha).1,Or.inl (hI.2.1 t z ha).2⟩
      · exact ⟨(hJ.2.1 t z hb).1,Or.inr (hJ.2.1 t z hb).2⟩
    · intro t ht
      by_cases hp : P t
      · obtain ⟨z,hz⟩ := hI.2.2 t ⟨ht.1,ht.2.1⟩
        exact ⟨z,Or.inl ⟨hp,hz⟩⟩
      · obtain ⟨z,hz⟩ := hJ.2.2 t ⟨ht.1,ht.2.2⟩
        exact ⟨z,Or.inr ⟨hp,hz⟩⟩

/-- Compositional integration with two successfully interpreted guarded branches.
This is an external selection combinator, not a new Expr constructor. -/
theorem select_guarded_branches_sound {c : BranchDecision} {P : ℝ → Prop}
    {X Y I J : LinearInterval} {D E : DomainBounds ℝ} {A B : ℝ → ℝ → Prop}
    {a b : Expr} (hc : BranchSound c P)
    (hX : (X.onDomain D).Sound A) (hY : (Y.onDomain E).Sound B)
    (ha : evalGuarded X Y a = some I) (hb : evalGuarded X Y b = some J) :
    ((selectLinear c I J).onDomain (selectDomain c (D.inter E) (D.inter E))).Sound
      (PiecewiseValues P (ExpressionValues A B a) (ExpressionValues A B b)) :=
  select_domain_sound hc (evalGuarded_relational_sound hX hY ha)
    (evalGuarded_relational_sound hX hY hb)

end GeneralizedIntervalArithmetic
