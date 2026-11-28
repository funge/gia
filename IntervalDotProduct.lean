import IntervalOps
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.BigOperators

/-! Exact finite dot-product bounds for independently chosen real coordinates.
The executable reference computes rational endpoints, not hardware floats. -/
namespace GeneralizedIntervalArithmetic.IntervalDotProduct
open scoped BigOperators

def dot {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i

def InBox {n : ℕ} (I : Fin n → QInterval) (x : Fin n → ℝ) : Prop :=
  ∀ i, (I i).Contains (x i)

/-- Sum the existing four-corner product bounds. All input intervals are finite,
closed and nonempty by construction; n=0 returns [0,0]. -/
def bounds {n : ℕ} (I J : Fin n → QInterval) : QInterval :=
  ⟨∑ i, ((I i).mul (J i)).lo, ∑ i, ((I i).mul (J i)).hi,
    Finset.sum_le_sum (fun i _ => ((I i).mul (J i)).ordered)⟩

theorem sound {n : ℕ} {I J : Fin n → QInterval} {x y : Fin n → ℝ}
    (hx : InBox I x) (hy : InBox J y) : (bounds I J).Contains (dot x y) := by
  constructor
  · simpa [bounds,dot] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (mul_encloses (hx i) (hy i)).1)
  · simpa [bounds,dot] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (mul_encloses (hx i) (hy i)).2)

/-- Every extremal product is realized by an endpoint pair. -/
theorem product_lower_attained (I J : QInterval) :
    ∃ x y : ℝ, I.Contains x ∧ J.Contains y ∧ x*y = ((I.mul J).lo : ℝ) := by
  have il : I.Contains (I.lo:ℝ) := ⟨le_rfl,by exact_mod_cast I.ordered⟩
  have iu : I.Contains (I.hi:ℝ) := ⟨by exact_mod_cast I.ordered,le_rfl⟩
  have jl : J.Contains (J.lo:ℝ) := ⟨le_rfl,by exact_mod_cast J.ordered⟩
  have ju : J.Contains (J.hi:ℝ) := ⟨by exact_mod_cast J.ordered,le_rfl⟩
  rcases min_choice (min (I.lo*J.lo) (I.lo*J.hi))
    (min (I.hi*J.lo) (I.hi*J.hi)) with h | h
  · rcases min_choice (I.lo*J.lo) (I.lo*J.hi) with h' | h'
    · exact ⟨I.lo,J.lo,il,jl,by simpa only [QInterval.mul,Rat.cast_mul] using (congrArg (fun q : ℚ => (q : ℝ)) (h.trans h')).symm⟩
    · exact ⟨I.lo,J.hi,il,ju,by simpa only [QInterval.mul,Rat.cast_mul] using (congrArg (fun q : ℚ => (q : ℝ)) (h.trans h')).symm⟩
  · rcases min_choice (I.hi*J.lo) (I.hi*J.hi) with h' | h'
    · exact ⟨I.hi,J.lo,iu,jl,by simpa only [QInterval.mul,Rat.cast_mul] using (congrArg (fun q : ℚ => (q : ℝ)) (h.trans h')).symm⟩
    · exact ⟨I.hi,J.hi,iu,ju,by simpa only [QInterval.mul,Rat.cast_mul] using (congrArg (fun q : ℚ => (q : ℝ)) (h.trans h')).symm⟩

theorem product_upper_attained (I J : QInterval) :
    ∃ x y : ℝ, I.Contains x ∧ J.Contains y ∧ x*y = ((I.mul J).hi : ℝ) := by
  have il : I.Contains (I.lo:ℝ) := ⟨le_rfl,by exact_mod_cast I.ordered⟩
  have iu : I.Contains (I.hi:ℝ) := ⟨by exact_mod_cast I.ordered,le_rfl⟩
  have jl : J.Contains (J.lo:ℝ) := ⟨le_rfl,by exact_mod_cast J.ordered⟩
  have ju : J.Contains (J.hi:ℝ) := ⟨by exact_mod_cast J.ordered,le_rfl⟩
  rcases max_choice (max (I.lo*J.lo) (I.lo*J.hi))
    (max (I.hi*J.lo) (I.hi*J.hi)) with h | h
  · rcases max_choice (I.lo*J.lo) (I.lo*J.hi) with h' | h'
    · exact ⟨I.lo,J.lo,il,jl,by simpa only [QInterval.mul,Rat.cast_mul] using (congrArg (fun q : ℚ => (q : ℝ)) (h.trans h')).symm⟩
    · exact ⟨I.lo,J.hi,il,ju,by simpa only [QInterval.mul,Rat.cast_mul] using (congrArg (fun q : ℚ => (q : ℝ)) (h.trans h')).symm⟩
  · rcases max_choice (I.hi*J.lo) (I.hi*J.hi) with h' | h'
    · exact ⟨I.hi,J.lo,iu,jl,by simpa only [QInterval.mul,Rat.cast_mul] using (congrArg (fun q : ℚ => (q : ℝ)) (h.trans h')).symm⟩
    · exact ⟨I.hi,J.hi,iu,ju,by simpa only [QInterval.mul,Rat.cast_mul] using (congrArg (fun q : ℚ => (q : ℝ)) (h.trans h')).symm⟩

theorem lower_attained {n : ℕ} (I J : Fin n → QInterval) :
    ∃ x y, InBox I x ∧ InBox J y ∧ dot x y = ((bounds I J).lo : ℝ) := by
  classical
  choose x y hx hy he using fun i => product_lower_attained (I i) (J i)
  exact ⟨x,y,hx,hy,by simp [dot,bounds,he]⟩

theorem upper_attained {n : ℕ} (I J : Fin n → QInterval) :
    ∃ x y, InBox I x ∧ InBox J y ∧ dot x y = ((bounds I J).hi : ℝ) := by
  classical
  choose x y hx hy he using fun i => product_upper_attained (I i) (J i)
  exact ⟨x,y,hx,hy,by simp [dot,bounds,he]⟩

/-- Least among all closed real interval enclosures, not only rational ones. -/
theorem least {n : ℕ} (I J : Fin n → QInterval) {l u : ℝ}
    (h : ∀ x y, InBox I x → InBox J y → l ≤ dot x y ∧ dot x y ≤ u) :
    l ≤ ((bounds I J).lo : ℝ) ∧ ((bounds I J).hi : ℝ) ≤ u := by
  obtain ⟨x,y,hx,hy,he⟩ := lower_attained I J
  obtain ⟨v,w,hv,hw,hf⟩ := upper_attained I J
  exact ⟨he ▸ (h x y hx hy).1,hf ▸ (h v w hv hw).2⟩

/-- Fixed rational weights are singleton intervals; inputs still denote reals. -/
def weightedBounds {n : ℕ} (w : Fin n → ℚ) (I : Fin n → QInterval) : QInterval :=
  bounds (fun i => QInterval.point (w i)) I

theorem weighted_sound {n : ℕ} (w : Fin n → ℚ) {I : Fin n → QInterval}
    {x : Fin n → ℝ} (hx : InBox I x) :
    (weightedBounds w I).Contains (dot (fun i => (w i : ℝ)) x) :=
  sound (fun _ => ⟨le_rfl,le_rfl⟩) hx

theorem weighted_extrema {n : ℕ} (w : Fin n → ℚ) (I : Fin n → QInterval) :
    (∃ x, InBox I x ∧ dot (fun i => (w i : ℝ)) x = ((weightedBounds w I).lo : ℝ)) ∧
    (∃ x, InBox I x ∧ dot (fun i => (w i : ℝ)) x = ((weightedBounds w I).hi : ℝ)) := by
  have fixed : ∀ v, InBox (fun i => QInterval.point (w i)) v → v = fun i => (w i : ℝ) := by
    intro v hv; funext i; exact le_antisymm (hv i).2 (hv i).1
  constructor
  · obtain ⟨v,x,hv,hx,he⟩ := lower_attained (fun i => QInterval.point (w i)) I
    exact ⟨x,hx,by simpa [fixed v hv,weightedBounds] using he⟩
  · obtain ⟨v,x,hv,hx,he⟩ := upper_attained (fun i => QInterval.point (w i)) I
    exact ⟨x,hx,by simpa [fixed v hv,weightedBounds] using he⟩

end GeneralizedIntervalArithmetic.IntervalDotProduct
