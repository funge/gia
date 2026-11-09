import LinearMultiplication
import Evaluator
import AuditPolicy

-- Experimental test-local representation, not an exported production interface.
namespace GeneralizedIntervalArithmetic.OptionalRangePrototype

structure Summary (Env : Type*) where
  domain : DomainBounds Env
  bounds : Option (FunctionalBounds Env)

def Summary.Sound {Env : Type*} (S : Summary Env) (R : Env → ℝ → Prop) : Prop :=
  (∀ p z, R p z → S.domain.possible p) ∧
  (∀ p, S.domain.definite p → ∃ z, R p z) ∧
  (∀ B, S.bounds = some B → ∀ p z, R p z → B.Contains p z)

def embed {Env : Type*} (I : PartialEnclosure Env) : Summary Env := ⟨I.domain, some I.values⟩

theorem embed_sound {Env : Type*} {I : PartialEnclosure Env} {R : Env → ℝ → Prop}
    (h : I.Sound R) : (embed I).Sound R := by
  refine ⟨h.2.1, h.2.2, ?_⟩
  intro B hb
  cases Option.some.inj hb
  exact h.1

def forgetRange {Env : Type*} (S : Summary Env) : Summary Env := ⟨S.domain, none⟩

theorem forget_sound {Env : Type*} {S : Summary Env} {R : Env → ℝ → Prop}
    (h : S.Sound R) : (forgetRange S).Sound R :=
  ⟨h.1, h.2.1, fun _ hb => by cases hb⟩

private theorem recover_sound {Env : Type*} {S : Summary Env} {R : Env → ℝ → Prop}
    (h : S.Sound R) {B : FunctionalBounds Env} (hb : S.bounds = some B) :
    (PartialEnclosure.mk B S.domain).Sound R := ⟨h.2.2 B hb, h.1, h.2.1⟩

theorem embedding_is_faithful {Env : Type*} (I : PartialEnclosure Env) (R : Env → ℝ → Prop) :
    (embed I).Sound R ↔ I.Sound R :=
  ⟨fun h => recover_sound h rfl, embed_sound⟩

-- Reuse existing addition when ranges are present; preserve the same environment
-- and domain conjunction when either range is unavailable.
def add {Env : Type*} (S T : Summary Env) : Summary Env :=
  match S.bounds, T.bounds with
  | some B, some C => embed ((PartialEnclosure.mk B S.domain).add ⟨C, T.domain⟩)
  | _, _ => ⟨S.domain.inter T.domain, none⟩

theorem add_sound {Env : Type*} {S T : Summary Env} {R U : Env → ℝ → Prop}
    (hs : S.Sound R) (ht : T.Sound U) : (add S T).Sound (SumValues R U) := by
  have hd : (Summary.mk (S.domain.inter T.domain) none).Sound (SumValues R U) := by
    refine ⟨?_, ?_, fun _ hb => by cases hb⟩
    · rintro p z ⟨x, y, hx, hy, _⟩
      exact ⟨hs.1 p x hx, ht.1 p y hy⟩
    · intro p hp
      obtain ⟨x, hx⟩ := hs.2.1 p hp.1
      obtain ⟨y, hy⟩ := ht.2.1 p hp.2
      exact ⟨x+y, x, y, hx, hy, rfl⟩
  unfold add
  split
  · rename_i B C hB hC
    exact embed_sound (partial_add_sound (recover_sound hs hB) (recover_sound ht hC))
  · exact hd

-- A full environment is fixed before either child is evaluated. Output witnesses
-- may be existential, but neither child can choose a different environment.
theorem shared_expression_sum {Env : Type*} (x y : Env → ℝ) (E : Env → Prop)
    (a b : Expr) (p : Env) (z : ℝ) :
    SumValues (fun p z => E p ∧ Value (x p) (y p) a z)
      (fun p z => E p ∧ Value (x p) (y p) b z) p z ↔
      E p ∧ Value (x p) (y p) (.add a b) z := by
  constructor
  · rintro ⟨u, v, ⟨he, hu⟩, ⟨_, hv⟩, rfl⟩
    exact ⟨he, Value.add hu hv⟩
  · rintro ⟨he, hv⟩
    cases hv with
    | add hu hv => exact ⟨_, _, ⟨he, hu⟩, ⟨he, hv⟩, rfl⟩

-- A hole can be known exactly while all numerical range information is absent.
def reciprocal : Summary ℝ :=
  ⟨⟨fun x => x ≠ 0, fun x => x ≠ 0, fun _ h => h⟩, none⟩
def Reciprocal (x z : ℝ) := x ≠ 0 ∧ z = x⁻¹

theorem reciprocal_sound : reciprocal.Sound Reciprocal :=
  ⟨fun _ _ h => h.1, fun x hx => ⟨x⁻¹, hx, rfl⟩, fun _ h => by cases h⟩
theorem reciprocal_semantics (x z : ℝ) :
    Reciprocal x z ↔ Value x 0 (.div (.const 1) .x) z := by
  constructor
  · rintro ⟨hx, rfl⟩
    have hv := Value.div (x := x) (y := (0:ℝ)) (Value.const 1) Value.x hx
    simpa [one_div] using hv
  · intro hv
    cases hv with
    | div ha hb hn =>
      cases ha
      cases hb
      exact ⟨hn, by simp⟩

theorem absent_range_but_present_value : reciprocal.bounds = none ∧ Reciprocal 1 1 := by
  norm_num [reciprocal, Reciprocal]
theorem pole_absent : ¬ ∃ z, Reciprocal 0 z := by simp [Reciprocal]

theorem addition_without_range_can_be_defined :
    (add reciprocal reciprocal).bounds = none ∧
      ∃ z, SumValues Reciprocal Reciprocal 1 z := by
  refine ⟨rfl, (add_sound reciprocal_sound reciprocal_sound).2.1 1 ?_⟩
  constructor <;> norm_num [reciprocal]

-- Disjoint child domains cannot manufacture a common environment.
def left : Summary ℝ := ⟨⟨fun x => x = -1, fun x => x = -1, fun _ h => h⟩, none⟩
def right : Summary ℝ := ⟨⟨fun x => x = 1, fun x => x = 1, fun _ h => h⟩, none⟩
def L (x z : ℝ) := x = -1 ∧ z = -1/2
def R (x z : ℝ) := x = 1 ∧ z = 1/2

theorem left_sound : left.Sound L :=
  ⟨fun _ _ h => h.1, fun _ h => ⟨-1/2, h, rfl⟩, fun _ h => by cases h⟩
theorem right_sound : right.Sound R :=
  ⟨fun _ _ h => h.1, fun _ h => ⟨1/2, h, rfl⟩, fun _ h => by cases h⟩
theorem each_child_exists : (∃ x z, L x z) ∧ (∃ x z, R x z) :=
  ⟨⟨-1, -1/2, rfl, rfl⟩, ⟨1, 1/2, rfl, rfl⟩⟩
theorem shared_sum_absent : ¬ ∃ x z, SumValues L R x z := by
  rintro ⟨x, z, hz⟩
  have h := (add_sound left_sound right_sound).1 x z hz
  change x = -1 ∧ x = 1 at h
  linarith [h.1, h.2]

-- Range availability and domain uncertainty are independent dimensions.
def uncertain : Summary Unit :=
  ⟨⟨fun _ => False, fun _ => True, fun _ h => h.elim⟩, none⟩
theorem unknown_empty_sound : uncertain.Sound (fun _ _ => False) :=
  ⟨fun _ _ h => h.elim, fun _ h => h.elim, fun _ h => by cases h⟩
theorem unknown_present_sound : uncertain.Sound (fun _ z => z = 0) :=
  ⟨fun _ _ _ => trivial, fun _ h => h.elim, fun _ h => by cases h⟩

end GeneralizedIntervalArithmetic.OptionalRangePrototype
#audit_namespace GeneralizedIntervalArithmetic.OptionalRangePrototype
