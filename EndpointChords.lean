import LinearIntervals
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace GeneralizedIntervalArithmetic.EndpointChords

/-- Endpoint interpolation in a normalized parameter, also defined on singletons. -/
def blend (a b t : ℝ) : ℝ := (1-t)*a+t*b

theorem blend_mem {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    blend a b t ∈ Set.Icc a b := by
  dsimp [blend]
  constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hab),
    mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab)]

theorem blend_mono {a b c d t : ℝ} (ha : a ≤ c) (hb : b ≤ d)
    (ht : t ∈ Set.Icc (0:ℝ) 1) : blend a b t ≤ blend c d t :=
  add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left hb ht.1)

theorem blend_affine (a b t m c : ℝ) :
    blend (m*a+c) (m*b+c) t = m*blend a b t+c := by dsimp [blend]; ring

theorem blend_singleton (a t : ℝ) : blend a a t = a := by dsimp [blend]; ring

/-- Every point of a nonempty finite closed interval has a normalized witness.
The singleton case is handled before any division. -/
theorem parameter_exists {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, blend a b t = x := by
  by_cases hab : a = b
  · subst b
    have hxa : x = a := le_antisymm hx.2 hx.1
    exact ⟨0,by norm_num,by simp [blend,hxa]⟩
  · have hpos : 0 < b-a := sub_pos.mpr (lt_of_le_of_ne (hx.1.trans hx.2) hab)
    refine ⟨(x-a)/(b-a),⟨div_nonneg (sub_nonneg.mpr hx.1) hpos.le,
      (div_le_one hpos).mpr (by linarith [hx.2])⟩,?_⟩
    dsimp [blend]
    field_simp
    ring

/-- Tupper §3.3.10, restricted to a real-valued convex function on a closed interval. -/
theorem convex_upper {f : ℝ → ℝ} {a b t : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    f (blend a b t) ≤ blend (f a) (f b) t := by
  exact hf.2 ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ (sub_nonneg.mpr ht.2) ht.1 (by ring)

/-- §3.3.12's lower-bound dual. -/
theorem concave_lower {f : ℝ → ℝ} {a b t : ℝ} (hab : a ≤ b)
    (hf : ConcaveOn ℝ (Set.Icc a b) f) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    blend (f a) (f b) t ≤ f (blend a b t) := by
  exact hf.2 ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ (sub_nonneg.mpr ht.2) ht.1 (by ring)

/-- Endpoint constraints alone put the exact chord below any affine majorant.
Convexity is only needed separately to show the chord itself is a majorant. -/
theorem least_affine_upper {f : ℝ → ℝ} {a b t m c : ℝ} (hab : a ≤ b)
    (hu : ∀ x ∈ Set.Icc a b, f x ≤ m*x+c) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    blend (f a) (f b) t ≤ m*blend a b t+c := by
  rw [← blend_affine]
  exact blend_mono (hu a ⟨le_rfl,hab⟩) (hu b ⟨hab,le_rfl⟩) ht

theorem greatest_affine_lower {f : ℝ → ℝ} {a b t m c : ℝ} (hab : a ≤ b)
    (hl : ∀ x ∈ Set.Icc a b, m*x+c ≤ f x) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    m*blend a b t+c ≤ blend (f a) (f b) t := by
  rw [← blend_affine]
  exact blend_mono (hl a ⟨le_rfl,hab⟩) (hl b ⟨hab,le_rfl⟩) ht

/-- The normalized exact chord is the restriction of an affine function of x.
For a singleton choose the constant affine function, with no division. -/
theorem affine_chord_exists (f : ℝ → ℝ) (a b : ℝ) :
    ∃ m c : ℝ, ∀ t, m*blend a b t+c = blend (f a) (f b) t := by
  by_cases hab : a = b
  · subst b
    exact ⟨0,f a,by intro t; simp [blend_singleton]⟩
  · refine ⟨(f b-f a)/(b-a), f a-((f b-f a)/(b-a))*a, ?_⟩
    intro t
    have hn : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    dsimp [blend]
    field_simp
    ring

/-- A pointwise least affine majorant on the entire interval, not merely an
undominated choice under a particular error measure. -/
theorem convex_optimal (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) :
    ∃ m c : ℝ, (∀ x ∈ Set.Icc a b, f x ≤ m*x+c) ∧
      (∀ n d : ℝ, (∀ x ∈ Set.Icc a b, f x ≤ n*x+d) →
        ∀ x ∈ Set.Icc a b, m*x+c ≤ n*x+d) := by
  obtain ⟨m,c,he⟩ := affine_chord_exists f a b
  refine ⟨m,c,?_,?_⟩
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := parameter_exists hx
    rw [he]
    exact convex_upper hab hf ht
  · intro n d hu x hx
    obtain ⟨t,ht,rfl⟩ := parameter_exists hx
    rw [he]
    exact least_affine_upper hab hu ht

theorem concave_optimal (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hf : ConcaveOn ℝ (Set.Icc a b) f) :
    ∃ m c : ℝ, (∀ x ∈ Set.Icc a b, m*x+c ≤ f x) ∧
      (∀ n d : ℝ, (∀ x ∈ Set.Icc a b, n*x+d ≤ f x) →
        ∀ x ∈ Set.Icc a b, n*x+d ≤ m*x+c) := by
  obtain ⟨m,c,he⟩ := affine_chord_exists f a b
  refine ⟨m,c,?_,?_⟩
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := parameter_exists hx
    rw [he]
    exact concave_lower hab hf ht
  · intro n d hl x hx
    obtain ⟨t,ht,rfl⟩ := parameter_exists hx
    rw [he]
    exact greatest_affine_lower hab hl ht

/-- Certified outward endpoint values preserve enclosure, not exact optimality. -/
theorem outward_upper {f : ℝ → ℝ} {a b t u v : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hu : f a ≤ u) (hv : f b ≤ v)
    (ht : t ∈ Set.Icc (0:ℝ) 1) : f (blend a b t) ≤ blend u v t :=
  (convex_upper hab hf ht).trans (blend_mono hu hv ht)

theorem outward_lower {f : ℝ → ℝ} {a b t l k : ℝ} (hab : a ≤ b)
    (hf : ConcaveOn ℝ (Set.Icc a b) f) (hl : l ≤ f a) (hk : k ≤ f b)
    (ht : t ∈ Set.Icc (0:ℝ) 1) : blend l k t ≤ f (blend a b t) :=
  (blend_mono hl hk ht).trans (concave_lower hab hf ht)

/-- Connect the real theorem to the existing rational endpoint representation. -/
theorem qaffine_upper {f : ℝ → ℝ} {a b t : ℝ} (u : QAffine) (hab : a ≤ b)
    (hf : ConvexOn ℝ (Set.Icc a b) f)
    (h0 : f a ≤ (u.atZero:ℝ)) (h1 : f b ≤ (u.atOne:ℝ))
    (ht : t ∈ Set.Icc (0:ℝ) 1) : f (blend a b t) ≤ u.value t :=
  outward_upper hab hf h0 h1 ht

theorem qaffine_lower {f : ℝ → ℝ} {a b t : ℝ} (l : QAffine) (hab : a ≤ b)
    (hf : ConcaveOn ℝ (Set.Icc a b) f)
    (h0 : (l.atZero:ℝ) ≤ f a) (h1 : (l.atOne:ℝ) ≤ f b)
    (ht : t ∈ Set.Icc (0:ℝ) 1) : l.value t ≤ f (blend a b t) :=
  outward_lower hab hf h0 h1 ht

theorem exact_singleton (f : ℝ → ℝ) (a t : ℝ) :
    blend (f a) (f a) t = f (blend a a t) := by rw [blend_singleton,blend_singleton]

/-- Source curvature annotations: the upper cubic branch is convex. -/
theorem cubic_upper_convex : ConvexOn ℝ (Set.Icc 0 1) (fun t : ℝ => (4-t)^3) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy s t hs ht hst
  have h := (convexOn_pow (𝕜 := ℝ) 3).2
    (show 4-x ∈ Set.Ici 0 by simp only [Set.mem_Ici]; linarith [hx.2])
    (show 4-y ∈ Set.Ici 0 by simp only [Set.mem_Ici]; linarith [hy.2]) hs ht hst
  simp only [smul_eq_mul] at *
  have he : s*(4-x)+t*(4-y) = 4-(s*x+t*y) := by nlinarith
  rwa [he] at h

/-- The lower cubic branch is concave, contrary to damaged transcription. -/
theorem cubic_lower_concave : ConcaveOn ℝ (Set.Icc 0 1) (fun t : ℝ => (-2+t)^3) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy s t hs ht hst
  have h := (convexOn_pow (𝕜 := ℝ) 3).2
    (show 2-x ∈ Set.Ici 0 by simp only [Set.mem_Ici]; linarith [hx.2])
    (show 2-y ∈ Set.Ici 0 by simp only [Set.mem_Ici]; linarith [hy.2]) hs ht hst
  simp only [smul_eq_mul] at *
  have he : s*(2-x)+t*(2-y) = 2-(s*x+t*y) := by nlinarith
  rw [he] at h
  have hn (z : ℝ) : (-2+z)^3 = -(2-z)^3 := by ring
  simp only [hn]
  nlinarith

/-- The §3.3.14 source example; curvature-specific residuals are nonnegative. -/
theorem cubic_source_enclosure {α x : ℝ} (hα : α ∈ Set.Icc (0:ℝ) 1)
    (hx : x ∈ Set.Icc (-2+α) (4-α)) : -8+7*α ≤ x^3 ∧ x^3 ≤ 64-37*α := by
  have hlow : (-2+α)^3 ≤ x^3 := (Odd.strictMono_pow (by decide : Odd 3)).monotone hx.1
  have hupp : x^3 ≤ (4-α)^3 := (Odd.strictMono_pow (by decide : Odd 3)).monotone hx.2
  have hl := concave_lower (by norm_num : (0:ℝ) ≤ 1) cubic_lower_concave hα
  have hu := convex_upper (by norm_num : (0:ℝ) ≤ 1) cubic_upper_convex hα
  norm_num [blend] at hl hu
  constructor <;> linarith

end GeneralizedIntervalArithmetic.EndpointChords
