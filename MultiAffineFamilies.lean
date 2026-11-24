import LinearFamilyEquality

/-! Finite rational instance of Tupper §2.9.6, sharing one whole parameter vector. -/
namespace GeneralizedIntervalArithmetic.MultiAffineFamilies
open scoped BigOperators

structure Form (n : ℕ) where
  offset : ℚ
  coeff : Fin n → ℚ

noncomputable def Cube {n : ℕ} (t : Fin n → ℝ) : Prop := ∀ i, t i ∈ Set.Icc (0:ℝ) 1
noncomputable def Form.value {n} (a : Form n) (t : Fin n → ℝ) : ℝ :=
  a.offset + ∑ i, (a.coeff i : ℝ) * t i

noncomputable def Form.lo {n} (a : Form n) : ℚ := a.offset + ∑ i, min 0 (a.coeff i)
noncomputable def Form.hi {n} (a : Form n) : ℚ := a.offset + ∑ i, max 0 (a.coeff i)
noncomputable def Form.lowCorner {n} (a : Form n) (i : Fin n) : ℝ := if a.coeff i < 0 then 1 else 0
noncomputable def Form.highCorner {n} (a : Form n) (i : Fin n) : ℝ := if a.coeff i < 0 then 0 else 1

theorem corners_in_cube {n} (a : Form n) : Cube a.lowCorner ∧ Cube a.highCorner := by
  constructor <;> intro i <;> simp only [Form.lowCorner,Form.highCorner] <;>
    split_ifs <;> norm_num

theorem attained_lo {n} (a : Form n) : a.value a.lowCorner = (a.lo:ℝ) := by
  simp only [Form.value,Form.lo,Rat.cast_add,Rat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : a.coeff i < 0
  · simp [Form.lowCorner,h,min_eq_right (le_of_lt h)]
  · simp [Form.lowCorner,h,min_eq_left (le_of_not_gt h)]

theorem attained_hi {n} (a : Form n) : a.value a.highCorner = (a.hi:ℝ) := by
  simp only [Form.value,Form.hi,Rat.cast_add,Rat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : a.coeff i < 0
  · simp [Form.highCorner,h,max_eq_left (le_of_lt h)]
  · simp [Form.highCorner,h,max_eq_right (le_of_not_gt h)]

theorem encloses {n} (a : Form n) {t} (ht : Cube t) :
    (a.lo:ℝ) ≤ a.value t ∧ a.value t ≤ (a.hi:ℝ) := by
  simp only [Form.value,Form.lo,Form.hi,Rat.cast_add,Rat.cast_sum]
  constructor <;> apply add_le_add_left <;> apply Finset.sum_le_sum <;> intro i hi
  · rw [Rat.cast_min,Rat.cast_zero]
    rcases le_total (0:ℝ) (a.coeff i) with h | h
    · rw [min_eq_left h]; exact mul_nonneg h (ht i).1
    · rw [min_eq_right h]; nlinarith [(ht i).1,(ht i).2]
  · rw [Rat.cast_max,Rat.cast_zero]
    rcases le_total (0:ℝ) (a.coeff i) with h | h
    · rw [max_eq_right h]; nlinarith [(ht i).1,(ht i).2]
    · rw [max_eq_left h]; exact mul_nonpos_of_nonpos_of_nonneg h (ht i).1

noncomputable def Form.sub {n} (a b : Form n) : Form n := ⟨a.offset-b.offset,fun i=>a.coeff i-b.coeff i⟩
noncomputable def Form.add {n} (a b : Form n) : Form n := ⟨a.offset+b.offset,fun i=>a.coeff i+b.coeff i⟩
noncomputable def Form.scale {n} (q : ℚ) (a : Form n) : Form n := ⟨q*a.offset,fun i=>q*a.coeff i⟩

theorem sub_value {n} (a b : Form n) (t) :
    (a.sub b).value t = a.value t - b.value t := by
  simp [Form.sub,Form.value,sub_mul,Finset.sum_sub_distrib]; ring

theorem add_value {n} (a b : Form n) (t) :
    (a.add b).value t = a.value t + b.value t := by
  simp [Form.add,Form.value,add_mul,Finset.sum_add_distrib]; ring

theorem scale_value {n} (q : ℚ) (a : Form n) (t) :
    (Form.scale q a).value t = (q:ℝ) * a.value t := by
  simp [Form.scale,Form.value,Finset.mul_sum,mul_add,mul_assoc]

/-- Exact rational criterion; no vertex enumeration or assumed order. -/
theorem order_iff {n} (a b : Form n) :
    (∀ t, Cube t → a.value t ≤ b.value t) ↔ (a.sub b).hi ≤ 0 := by
  constructor
  · intro h
    have hh := h (a.sub b).highCorner (corners_in_cube _).2
    have he := attained_hi (a.sub b)
    rw [sub_value] at he
    have : ((a.sub b).hi:ℝ) ≤ 0 := by linarith
    exact_mod_cast this
  · intro h t ht
    have hh := (encloses (a.sub b) ht).2
    rw [sub_value] at hh
    have : ((a.sub b).hi:ℝ) ≤ 0 := by exact_mod_cast h
    linarith

structure Bounds (n : ℕ) where
  lower : Form n
  upper : Form n
  noncollapse : (lower.sub upper).hi ≤ 0

noncomputable def Bounds.Contains {n} (I : Bounds n) (t : Fin n → ℝ) (z : ℝ) : Prop :=
  I.lower.value t ≤ z ∧ z ≤ I.upper.value t

theorem bounds_ordered {n} (I : Bounds n) {t} (ht : Cube t) :
    I.lower.value t ≤ I.upper.value t := (order_iff _ _).mpr I.noncollapse t ht

noncomputable def Bounds.hull {n} (I : Bounds n) : QInterval :=
  ⟨I.lower.lo,I.upper.hi,by
    have h := (encloses I.lower (corners_in_cube I.lower).1).1
    have k := (encloses I.upper (corners_in_cube I.lower).1).2
    have o := bounds_ordered I (corners_in_cube I.lower).1
    exact_mod_cast (le_trans h (le_trans o k))⟩

theorem hull_encloses {n} (I : Bounds n) {t z} (ht : Cube t) (hz : I.Contains t z) :
    I.hull.Contains z :=
  ⟨(encloses I.lower ht).1.trans hz.1,hz.2.trans (encloses I.upper ht).2⟩

theorem hull_endpoints_attained {n} (I : Bounds n) :
    I.Contains I.lower.lowCorner (I.hull.lo:ℝ) ∧
    I.Contains I.upper.highCorner (I.hull.hi:ℝ) := by
  constructor
  · change I.lower.value _ ≤ (I.lower.lo:ℝ) ∧ (I.lower.lo:ℝ) ≤ I.upper.value _
    rw [← attained_lo]
    exact ⟨le_rfl,bounds_ordered I (corners_in_cube _).1⟩
  · change I.lower.value _ ≤ (I.upper.hi:ℝ) ∧ (I.upper.hi:ℝ) ≤ I.upper.value _
    rw [← attained_hi]
    exact ⟨bounds_ordered I (corners_in_cube _).2,le_rfl⟩

theorem hull_least {n} (I : Bounds n) {l u : ℝ}
    (h : ∀ t, Cube t → ∀ z, I.Contains t z → z ∈ Set.Icc l u) :
    ∀ z, I.hull.Contains z → z ∈ Set.Icc l u := by
  have hl := h _ (corners_in_cube I.lower).1 _ (hull_endpoints_attained I).1
  have hu := h _ (corners_in_cube I.upper).2 _ (hull_endpoints_attained I).2
  exact fun z hz=>⟨hl.1.trans hz.1,hz.2.trans hu.2⟩

theorem constant_demotion {n} (I : Bounds n) :
    GeneralFamilyDemotion.Demotes (fun t=>{z|I.Contains t z})
      (DomainConstraints.exactDomain Cube) (fun _=>{z|I.hull.Contains z})
      (DomainConstraints.exactDomain Cube) :=
  ⟨fun _=>⟨id,id⟩,fun _ ht _ hz=>hull_encloses I ht hz⟩

/-- Exact correspondence with the established one-parameter endpoint basis. -/
noncomputable def fromQAffine (a : QAffine) : Form 1 := ⟨a.atZero,fun _=>a.atOne-a.atZero⟩
theorem fromQAffine_value (a : QAffine) (t : Fin 1 → ℝ) :
    (fromQAffine a).value t = a.value (t 0) := by
  simp [fromQAffine,Form.value,QAffine.value]; ring

theorem inclusion_iff {n} (I J : Bounds n) :
    (∀ t, Cube t → ∀ z, I.Contains t z → J.Contains t z) ↔
    (J.lower.sub I.lower).hi ≤ 0 ∧ (I.upper.sub J.upper).hi ≤ 0 := by
  constructor
  · intro h
    constructor <;> apply (order_iff _ _).mp <;> intro t ht
    · exact (h t ht _ ⟨le_rfl,bounds_ordered I ht⟩).1
    · exact (h t ht _ ⟨bounds_ordered I ht,le_rfl⟩).2
  · rintro ⟨hl,hu⟩ t ht z hz
    exact ⟨((order_iff _ _).mpr hl t ht).trans hz.1,
      hz.2.trans ((order_iff _ _).mpr hu t ht)⟩

noncomputable def Bounds.range {n} (I : Bounds n) : Set ℝ := {z|∃t,Cube t ∧ I.Contains t z}

theorem hull_exact {n} (I : Bounds n) :
    ExtendedImageHull.hull I.range = {z|I.hull.Contains z} := by
  have hb : I.range ⊆ {z|I.hull.Contains z} := by
    rintro z ⟨t,ht,hz⟩; exact hull_encloses I ht hz
  apply Set.Subset.antisymm
  · have hh := ExtendedImageHull.least (l := ((I.hull.lo:ℝ):EReal))
        (u := ((I.hull.hi:ℝ):EReal))
        (show I.range ⊆ ExtendedImageHull.interval ((I.hull.lo:ℝ):EReal) ((I.hull.hi:ℝ):EReal) by
          simpa [ExtendedImageHull.interval,QInterval.Contains] using hb)
    simpa [ExtendedImageHull.interval,QInterval.Contains] using hh
  · have hn : I.range.Nonempty :=
      ⟨_,I.lower.lowCorner,(corners_in_cube _).1,(hull_endpoints_attained I).1⟩
    have hl : BddBelow I.range := ⟨I.hull.lo,fun _ hz=>(hb hz).1⟩
    have hu : BddAbove I.range := ⟨I.hull.hi,fun _ hz=>(hb hz).2⟩
    rw [ExtendedImageHull.finite_agreement hn hl hu]
    apply hull_least I
    intro t ht z hz
    exact ExactImageHull.sound hl hu ⟨t,ht,hz⟩

noncomputable def fromLinear (I : LinearInterval) : Bounds 1 :=
  ⟨fromQAffine I.lower,fromQAffine I.upper,by
    apply (order_iff _ _).mp
    intro t ht
    rw [fromQAffine_value,fromQAffine_value]
    exact linear_ordered I (ht 0)⟩

theorem fromLinear_contains (I : LinearInterval) (t : Fin 1 → ℝ) (z : ℝ) :
    (fromLinear I).Contains t z ↔ I.Contains (t 0) z := by
  simp [Bounds.Contains,fromLinear,fromQAffine_value,LinearInterval.Contains]

/-- Existing one-parameter pointwise equality survives the embedding, without
asserting that the one-dimensional canonical alternative applies to a cube. -/
theorem fromLinear_equality (I J : LinearInterval)
    (h : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z, I.Contains t z ↔ J.Contains t z) :
    ∀ t, Cube t → ∀ z, (fromLinear I).Contains t z ↔ (fromLinear J).Contains t z := by
  intro t ht z
  rw [fromLinear_contains,fromLinear_contains]
  exact h _ (ht 0) z

end GeneralizedIntervalArithmetic.MultiAffineFamilies
