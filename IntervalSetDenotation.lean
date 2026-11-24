import NumberPromotion

/-! Tupper §2.13 existential piece semantics, at one shared parameter.
No finiteness, totality, domain flags or exceptional values are inferred. -/
namespace GeneralizedIntervalArithmetic.IntervalSetDenotation

variable {α Y : Type*}
def denote (V : Y → α → Set ℝ) (J : Set Y) (p : α) : Set ℝ :=
  {z | ∃ j ∈ J, z ∈ V j p}

theorem empty (V : Y → α → Set ℝ) (p : α) : denote V ∅ p = ∅ := by
  ext z; simp [denote]
theorem singleton (V : Y → α → Set ℝ) (j : Y) (p : α) :
    denote V {j} p = V j p := by ext z; simp [denote]
theorem union (V : Y → α → Set ℝ) (J K : Set Y) (p : α) :
    denote V (J ∪ K) p = denote V J p ∪ denote V K p := by
  ext z; simp only [denote, Set.mem_setOf_eq, Set.mem_union]; aesop

/-- Description intersection gives only inclusion; distinct descriptions may overlap. -/
theorem description_inter {V : Y → α → Set ℝ} (J K : Set Y) (p : α) :
    denote V (J ∩ K) p ⊆ denote V J p ∩ denote V K p := by
  rintro z ⟨j,hj,hz⟩
  exact ⟨⟨j,hj.1,hz⟩,⟨j,hj.2,hz⟩⟩

/-- Pairwise intersection, rather than intersection of description identifiers. -/
theorem pairwise_inter (V : Y → α → Set ℝ) (J K : Set Y) (p : α) :
    denote (fun jk : Y × Y => fun q => V jk.1 q ∩ V jk.2 q)
      (J ×ˢ K) p = denote V J p ∩ denote V K p := by
  ext z
  constructor
  · rintro ⟨⟨j,k⟩,⟨hj,hk⟩,⟨hz,hw⟩⟩
    exact ⟨⟨j,hj,hz⟩,⟨k,hk,hw⟩⟩
  · rintro ⟨⟨j,hj,hz⟩,⟨k,hk,hw⟩⟩
    exact ⟨(j,k),⟨hj,hk⟩,⟨hz,hw⟩⟩

/-- Exact point representation of a partial function, potentially infinite.
The equality guard retains the SAME parameter; absent outputs create no points. -/
def point (g : α → Option ℝ) (q p : α) : Set ℝ := {z | p = q ∧ g q = some z}

theorem points_exact (g : α → Option ℝ) (p : α) :
    denote (point g) Set.univ p = {z | g p = some z} := by
  ext z
  simp [denote,point]

theorem absent_points (g : α → Option ℝ) (p : α) (h : g p = none) :
    denote (point g) Set.univ p = ∅ := by rw [points_exact]; simp [h]

/-- Leastness concerns the one-interval target, not the original set family. -/
theorem real_projection (V : Y → α → Set ℝ) (J : Set Y) (p : α) :
    denote V J p ⊆ ExtendedImageHull.hull (denote V J p) ∧
    ∀ l u, denote V J p ⊆ ExtendedImageHull.interval l u →
      ExtendedImageHull.hull (denote V J p) ⊆ ExtendedImageHull.interval l u :=
  ⟨ExtendedImageHull.sound _, fun _ _ h => ExtendedImageHull.least h⟩

theorem integer_projection (V : Y → α → Set ℝ) (J : Set Y) (p : α) :
    denote V J p ⊆ NumberPromotion.hull (denote V J p) ∧
    ∀ l u, NumberPromotion.IntegerBound l → NumberPromotion.IntegerBound u →
      denote V J p ⊆ ExtendedImageHull.interval l u →
      NumberPromotion.hull (denote V J p) ⊆ ExtendedImageHull.interval l u :=
  ⟨NumberPromotion.sound _, fun _ _ hl hu h => NumberPromotion.least hl hu h⟩

/-- Equal real bounds in §2.14 give a singleton, not uncertain coefficients. -/
theorem equal_real_bounds (r : ℝ) :
    ExtendedImageHull.interval (r : EReal) r = {r} := by
  ext x
  simp [ExtendedImageHull.interval, ← le_antisymm_iff, eq_comm]

/-- Re-encoding pieces with identical pointwise meaning preserves the set meaning. -/
theorem reencode {Z : Type*} (V : Y → α → Set ℝ) (W : Z → α → Set ℝ)
    (f : Y → Z) (h : ∀ j p, W (f j) p = V j p) (J : Set Y) (p : α) :
    denote W (f '' J) p = denote V J p := by
  ext z
  simp only [denote, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨_,⟨j,hj,rfl⟩,hz⟩
    exact ⟨j,hj,by simpa [h] using hz⟩
  · rintro ⟨j,hj,hz⟩
    exact ⟨f j,⟨j,hj,rfl⟩,by simpa [h] using hz⟩
end GeneralizedIntervalArithmetic.IntervalSetDenotation
