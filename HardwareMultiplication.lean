import IntervalOps
import HardwareAddition

namespace GeneralizedIntervalArithmetic.HardwareMultiplication

/-- Four outward-rounded corner bounds enclose every product. The minima and
maxima here are mathematical real operations, not an assumed native selector. -/
theorem rounded_corners_enclose {a b c d x y l₁ l₂ l₃ l₄ u₁ u₂ u₃ u₄ : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (h₁ : l₁ ≤ a*c ∧ a*c ≤ u₁) (h₂ : l₂ ≤ a*d ∧ a*d ≤ u₂)
    (h₃ : l₃ ≤ b*c ∧ b*c ≤ u₃) (h₄ : l₄ ≤ b*d ∧ b*d ≤ u₄) :
    min (min l₁ l₂) (min l₃ l₄) ≤ x*y ∧
    x*y ≤ max (max u₁ u₂) (max u₃ u₄) := by
  have h := four_products hx hy
  exact ⟨(min_le_min (min_le_min h₁.1 h₂.1) (min_le_min h₃.1 h₄.1)).trans h.1,
    h.2.trans (max_le_max (max_le_max h₁.2 h₂.2) (max_le_max h₃.2 h₄.2))⟩

/-- A selector need only produce outer bounds, not necessarily the tight extrema.
These are explicit result obligations, not facts asserted about Float comparisons. -/
theorem selected_bounds_enclose {a b c d x y l₁ l₂ l₃ l₄ u₁ u₂ u₃ u₄ lo hi : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (h₁ : l₁ ≤ a*c ∧ a*c ≤ u₁) (h₂ : l₂ ≤ a*d ∧ a*d ≤ u₂)
    (h₃ : l₃ ≤ b*c ∧ b*c ≤ u₃) (h₄ : l₄ ≤ b*d ∧ b*d ≤ u₄)
    (hl : lo ≤ min (min l₁ l₂) (min l₃ l₄))
    (hu : max (max u₁ u₂) (max u₃ u₄) ≤ hi) : lo ≤ x*y ∧ x*y ≤ hi := by
  have h := rounded_corners_enclose hx hy h₁ h₂ h₃ h₄
  exact ⟨hl.trans h.1, h.2.trans hu⟩

open HardwareAddition

/-- Successful observed primitive multiplication encloses the real product. -/
def CallSound {F : Type} (decode : F → Option ℝ) (a b : F)
    (result : Option (F × F)) : Prop :=
  ∀ x y, decode a = some x → decode b = some y →
  ∀ p, result = some p → ∃ l u,
    decode p.1 = some l ∧ decode p.2 = some u ∧ l ≤ x*y ∧ x*y ≤ u

/-- Approved finite selection contract. It says nothing about NaNs/infinities or
which signed zero is selected when both inputs denote mathematical zero. -/
def SelectSound {F : Type} (decode : F → Option ℝ) (select : F → F → F)
    (op : ℝ → ℝ → ℝ) : Prop :=
  ∀ a b x y, decode a = some x → decode b = some y →
    decode (select a b) = some (op x y)

/-- A successful observed pair encloses one real corner value. -/
def ResultSound {F : Type} (decode : F → Option ℝ) (result : Option (F × F))
    (v : ℝ) : Prop := ∀ p, result = some p →
    ∃ l u, decode p.1 = some l ∧ decode p.2 = some u ∧ l ≤ v ∧ v ≤ u

/-- Generic decoded hull assembly, reused by multiplication and division. -/
theorem assembleFour_encloses_values {F : Type} {decode : F → Option ℝ}
    {chooseMin chooseMax : F → F → F}
    (hmin : SelectSound decode chooseMin min) (hmax : SelectSound decode chooseMax max)
    {R : Bounds F} {ll lh hl hh : Option (F × F)} {v₁ v₂ v₃ v₄ z : ℝ}
    (h₁ : ResultSound decode ll v₁) (h₂ : ResultSound decode lh v₂)
    (h₃ : ResultSound decode hl v₃) (h₄ : ResultSound decode hh v₄)
    (hz : min (min v₁ v₂) (min v₃ v₄) ≤ z ∧ z ≤ max (max v₁ v₂) (max v₃ v₄))
    (hr : assembleFour chooseMin chooseMax ll lh hl hh = some R) :
    Contains decode R z := by
  cases ll with
  | none => simp [assembleFour] at hr
  | some p₁ =>
    cases lh with
    | none => simp [assembleFour] at hr
    | some p₂ =>
      cases hl with
      | none => simp [assembleFour] at hr
      | some p₃ =>
        cases hh with
        | none => simp [assembleFour] at hr
        | some p₄ =>
          simp [assembleFour] at hr
          subst R
          rcases h₁ p₁ rfl with ⟨l₁, u₁, dl₁, du₁, b₁⟩
          rcases h₂ p₂ rfl with ⟨l₂, u₂, dl₂, du₂, b₂⟩
          rcases h₃ p₃ rfl with ⟨l₃, u₃, dl₃, du₃, b₃⟩
          rcases h₄ p₄ rfl with ⟨l₄, u₄, dl₄, du₄, b₄⟩
          refine ⟨min (min l₁ l₂) (min l₃ l₄), max (max u₁ u₂) (max u₃ u₄), ?_, ?_, ?_, ?_⟩
          · exact hmin _ _ _ _ (hmin _ _ _ _ dl₁ dl₂) (hmin _ _ _ _ dl₃ dl₄)
          · exact hmax _ _ _ _ (hmax _ _ _ _ du₁ du₂) (hmax _ _ _ _ du₃ du₄)
          · exact (min_le_min (min_le_min b₁.1 b₂.1) (min_le_min b₃.1 b₄.1)).trans hz.1
          · exact hz.2.trans (max_le_max (max_le_max b₁.2 b₂.2) (max_le_max b₃.2 b₄.2))

theorem assembleFour_encloses {F : Type} {decode : F → Option ℝ}
    {chooseMin chooseMax : F → F → F}
    (hmin : SelectSound decode chooseMin min) (hmax : SelectSound decode chooseMax max)
    {I J R : Bounds F} {ll lh hl hh : Option (F × F)}
    (hll : CallSound decode I.lo J.lo ll) (hlh : CallSound decode I.lo J.hi lh)
    (hhl : CallSound decode I.hi J.lo hl) (hhh : CallSound decode I.hi J.hi hh)
    (hr : assembleFour chooseMin chooseMax ll lh hl hh = some R)
    {x y : ℝ} (hx : Contains decode I x) (hy : Contains decode J y) :
    Contains decode R (x*y) := by
  rcases hx with ⟨a, b, ha, hb, hx⟩
  rcases hy with ⟨c, d, hc, hd, hy⟩
  exact assembleFour_encloses_values hmin hmax
    (hll a c ha hc) (hlh a d ha hd) (hhl b c hb hc) (hhh b d hb hd)
    (four_products hx hy) hr

end GeneralizedIntervalArithmetic.HardwareMultiplication
