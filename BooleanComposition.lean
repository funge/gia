import StrictComparison

/-! Finite Boolean images derived from Tupper §2.9.2 (printed p.27).
Reuse the existing nonempty Boolean intervals. Independent image equality
must not be transferred to correlated valuations. -/
namespace GeneralizedIntervalArithmetic.BooleanComposition
open StrictComparison

def neg : Truth → Truth
  | .falseOnly => .trueOnly
  | .both => .both
  | .trueOnly => .falseOnly

def conj : Truth → Truth → Truth
  | .falseOnly, _ => .falseOnly
  | _, .falseOnly => .falseOnly
  | .trueOnly, v => v
  | v, .trueOnly => v
  | .both, .both => .both

def disj : Truth → Truth → Truth
  | .trueOnly, _ => .trueOnly
  | _, .trueOnly => .trueOnly
  | .falseOnly, v => v
  | v, .falseOnly => v
  | .both, .both => .both

/-- Independent inputs: each operand has its own witness. -/
def image₂ (op : Bool → Bool → Bool) (A B : Set Bool) : Set Bool :=
  {r | ∃ a ∈ A, ∃ b ∈ B, op a b = r}

/-- A joint relation can retain correlation, holes, or an external domain. -/
def jointImage (op : Bool → Bool → Bool) (R : Bool → Bool → Prop) : Set Bool :=
  {r | ∃ a b, R a b ∧ op a b = r}

theorem neg_exact (v : Truth) :
    (neg v).values = Bool.not '' v.values := by
  cases v <;> ext b <;> cases b <;>
    simp [neg, Truth.values, Set.mem_image, Bool.exists_bool]

theorem conj_exact (v w : Truth) :
    (conj v w).values = image₂ Bool.and v.values w.values := by
  cases v <;> cases w <;> ext b <;> cases b <;>
    simp [conj, Truth.values, image₂, Bool.exists_bool]

theorem disj_exact (v w : Truth) :
    (disj v w).values = image₂ Bool.or v.values w.values := by
  cases v <;> cases w <;> ext b <;> cases b <;>
    simp [disj, Truth.values, image₂, Bool.exists_bool]

/-- Soundness for a joint relation is inclusion, with no attainment conclusion. -/
theorem joint_subset {op : Bool → Bool → Bool} {R : Bool → Bool → Prop}
    {A B : Set Bool} (h : ∀ a b, R a b → a ∈ A ∧ b ∈ B) :
    jointImage op R ⊆ image₂ op A B := by
  rintro r ⟨a, b, hab, hr⟩
  exact ⟨a, (h a b hab).1, b, (h a b hab).2, hr⟩

theorem joint_conj_sound {R : Bool → Bool → Prop} {v w : Truth}
    (h : ∀ a b, R a b → a ∈ v.values ∧ b ∈ w.values) :
    jointImage Bool.and R ⊆ (conj v w).values := by
  rw [conj_exact]
  exact joint_subset h

theorem joint_disj_sound {R : Bool → Bool → Prop} {v w : Truth}
    (h : ∀ a b, R a b → a ∈ v.values ∧ b ∈ w.values) :
    jointImage Bool.or R ⊆ (disj v w).values := by
  rw [disj_exact]
  exact joint_subset h

/-- Both Boolean operands refer to the same admissible input witness. -/
theorem shared_witness_sound {α : Type*} (D : Set α) (p q : α → Bool)
    {v w : Truth} (hp : ∀ x ∈ D, p x ∈ v.values)
    (hq : ∀ x ∈ D, q x ∈ w.values) :
    (fun x => p x && q x) '' D ⊆ (conj v w).values ∧
    (fun x => p x || q x) '' D ⊆ (disj v w).values := by
  constructor
  · rintro r ⟨x, hx, hr⟩
    rw [conj_exact]
    exact ⟨p x, hp x hx, q x, hq x hx, hr⟩
  · rintro r ⟨x, hx, hr⟩
    rw [disj_exact]
    exact ⟨p x, hp x hx, q x, hq x hx, hr⟩

theorem comparison_conj_exact (I J K L : QInterval) :
    (conj (StrictComparison.compare I J) (StrictComparison.compare K L)).values =
      image₂ Bool.and (outcomes I J) (outcomes K L) := by
  rw [conj_exact, compare_exact, compare_exact]

theorem comparison_disj_exact (I J K L : QInterval) :
    (disj (StrictComparison.compare I J) (StrictComparison.compare K L)).values =
      image₂ Bool.or (outcomes I J) (outcomes K L) := by
  rw [disj_exact, compare_exact, compare_exact]

theorem comparison_neg_exact (I J : QInterval) :
    (neg (StrictComparison.compare I J)).values = Bool.not '' outcomes I J := by
  rw [neg_exact, compare_exact]

theorem neg_involutive (v : Truth) : neg (neg v) = v := by cases v <;> rfl

theorem conj_comm (v w : Truth) : conj v w = conj w v := by
  cases v <;> cases w <;> rfl

theorem disj_comm (v w : Truth) : disj v w = disj w v := by
  cases v <;> cases w <;> rfl

theorem conj_assoc (u v w : Truth) : conj (conj u v) w = conj u (conj v w) := by
  cases u <;> cases v <;> cases w <;> rfl

theorem disj_assoc (u v w : Truth) : disj (disj u v) w = disj u (disj v w) := by
  cases u <;> cases v <;> cases w <;> rfl

theorem identities (v : Truth) : conj .trueOnly v = v ∧ disj .falseOnly v = v := by
  cases v <;> exact ⟨rfl, rfl⟩

theorem distributive (u v w : Truth) :
    conj u (disj v w) = disj (conj u v) (conj u w) ∧
    disj u (conj v w) = conj (disj u v) (disj u w) := by
  cases u <;> cases v <;> cases w <;> exact ⟨rfl, rfl⟩

theorem deMorgan (v w : Truth) :
    neg (conj v w) = disj (neg v) (neg w) ∧
    neg (disj v w) = conj (neg v) (neg w) := by
  cases v <;> cases w <;> exact ⟨rfl, rfl⟩

end GeneralizedIntervalArithmetic.BooleanComposition
