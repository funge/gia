import MultiAffineFamilies
import LinearMultiplication

/-! Finite quadratic forms. The one-parameter instance matches §2.9.5;
finite cross terms are an explicitly derived shared-vector extension. -/
namespace GeneralizedIntervalArithmetic.QuadraticFamilies
open scoped BigOperators
open MultiAffineFamilies

structure Form (n : ℕ) where
  affine : MultiAffineFamilies.Form n
  cross : Fin n → Fin n → ℚ

noncomputable def Form.value {n} (a : Form n) (t : Fin n → ℝ) : ℝ :=
  a.affine.value t + ∑ i, ∑ j, (a.cross i j:ℝ) * t i * t j
noncomputable def embed {n} (a : MultiAffineFamilies.Form n) : Form n := ⟨a,fun _ _=>0⟩
theorem embed_value {n} (a : MultiAffineFamilies.Form n) (t) :
    (embed a).value t = a.value t := by simp [embed,Form.value]

theorem embed_injective {n} : Function.Injective (@embed n) := by
  intro a b h
  exact congrArg Form.affine h

noncomputable def product {n} (a b : MultiAffineFamilies.Form n) : Form n :=
  ⟨⟨a.offset*b.offset,fun i=>a.offset*b.coeff i+a.coeff i*b.offset⟩,
   fun i j=>a.coeff i*b.coeff j⟩

theorem product_value {n} (a b : MultiAffineFamilies.Form n) (t) :
    (product a b).value t = a.value t*b.value t := by
  simp only [product,Form.value,MultiAffineFamilies.Form.value,
    Rat.cast_add,Rat.cast_mul,add_mul,Finset.sum_add_distrib]
  simp only [mul_add,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  ring_nf
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

noncomputable def Form.add {n} (a b : Form n) : Form n :=
  ⟨a.affine.add b.affine,fun i j=>a.cross i j+b.cross i j⟩
noncomputable def Form.sub {n} (a b : Form n) : Form n :=
  ⟨a.affine.sub b.affine,fun i j=>a.cross i j-b.cross i j⟩
noncomputable def Form.scale {n} (q : ℚ) (a : Form n) : Form n :=
  ⟨MultiAffineFamilies.Form.scale q a.affine,fun i j=>q*a.cross i j⟩

theorem add_value {n} (a b : Form n) (t) : (a.add b).value t = a.value t+b.value t := by
  simp [Form.add,Form.value,MultiAffineFamilies.add_value,add_mul,Finset.sum_add_distrib]; ring

theorem sub_value {n} (a b : Form n) (t) : (a.sub b).value t = a.value t-b.value t := by
  simp [Form.sub,Form.value,MultiAffineFamilies.sub_value,sub_mul,Finset.sum_sub_distrib]; ring

theorem scale_value {n} (q : ℚ) (a : Form n) (t) :
    (Form.scale q a).value t = (q:ℝ)*a.value t := by
  simp [Form.scale,Form.value,MultiAffineFamilies.scale_value,
    mul_add,Finset.mul_sum,mul_assoc]

noncomputable def ofCoefficients (p q r : ℚ) : Form 1 := ⟨⟨p,fun _=>q⟩,fun _ _=>r⟩
theorem coefficients_value (p q r : ℚ) (t : Fin 1 → ℝ) :
    (ofCoefficients p q r).value t = (p:ℝ)+(q:ℝ)*t 0+(r:ℝ)*(t 0)^2 := by
  simp [ofCoefficients,Form.value,MultiAffineFamilies.Form.value]; ring

theorem one_parameter_representation (a : Form 1) (t : Fin 1 → ℝ) :
    a.value t = (ofCoefficients a.affine.offset (a.affine.coeff 0) (a.cross 0 0)).value t := by
  simp [Form.value,ofCoefficients,MultiAffineFamilies.Form.value]

/-- Every monomial is in [0,1]; their independent use is only an enclosure. -/
theorem term_bounds (r x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    min 0 r ≤ r*x ∧ r*x ≤ max 0 r := by
  rcases le_total 0 r with h | h
  · rw [min_eq_left h,max_eq_right h]
    exact ⟨mul_nonneg h hx.1,by nlinarith [hx.2]⟩
  · rw [min_eq_right h,max_eq_left h]
    exact ⟨by nlinarith [hx.2],mul_nonpos_of_nonpos_of_nonneg h hx.1⟩

noncomputable def Form.lo {n} (a : Form n) : ℚ :=
  a.affine.lo + ∑ i, ∑ j, min 0 (a.cross i j)
noncomputable def Form.hi {n} (a : Form n) : ℚ :=
  a.affine.hi + ∑ i, ∑ j, max 0 (a.cross i j)

theorem encloses {n} (a : Form n) {t} (ht : Cube t) :
    (a.lo:ℝ) ≤ a.value t ∧ a.value t ≤ (a.hi:ℝ) := by
  have mono (i j : Fin n) : t i*t j ∈ Set.Icc (0:ℝ) 1 :=
    ⟨mul_nonneg (ht i).1 (ht j).1,
      by nlinarith [mul_le_mul (ht i).2 (ht j).2 (ht j).1 (by norm_num : (0:ℝ)≤1)]⟩
  simp only [Form.lo,Form.hi,Form.value,Rat.cast_add,Rat.cast_sum]
  constructor
  · apply add_le_add (MultiAffineFamilies.encloses a.affine ht).1
    apply Finset.sum_le_sum; intro i hi
    apply Finset.sum_le_sum; intro j hj
    simpa [Rat.cast_min,mul_assoc] using (term_bounds (a.cross i j) (t i*t j) (mono i j)).1
  · apply add_le_add (MultiAffineFamilies.encloses a.affine ht).2
    apply Finset.sum_le_sum; intro i hi
    apply Finset.sum_le_sum; intro j hj
    simpa [Rat.cast_max,mul_assoc] using (term_bounds (a.cross i j) (t i*t j) (mono i j)).2

structure Bounds (n : ℕ) where
  lower : Form n
  upper : Form n
  ordered : ∀ t, Cube t → lower.value t ≤ upper.value t

noncomputable def Bounds.Contains {n} (I : Bounds n) (t : Fin n → ℝ) (z : ℝ) : Prop :=
  I.lower.value t ≤ z ∧ z ≤ I.upper.value t
noncomputable def Bounds.constantHull {n} (I : Bounds n) : QInterval :=
  ⟨I.lower.lo,I.upper.hi,by
    have ht : Cube (fun _ : Fin n=>0) := fun _=>by norm_num
    have h := (encloses I.lower ht).1
    have k := (encloses I.upper ht).2
    have o := I.ordered _ ht
    exact_mod_cast (h.trans (o.trans k))⟩

theorem demotion_encloses {n} (I : Bounds n) {t z} (ht : Cube t) (hz : I.Contains t z) :
    I.constantHull.Contains z := ⟨(encloses I.lower ht).1.trans hz.1,hz.2.trans (encloses I.upper ht).2⟩

theorem constant_demotion {n} (I : Bounds n) :
    GeneralFamilyDemotion.Demotes (fun t=>{z|I.Contains t z})
      (DomainConstraints.exactDomain Cube) (fun _=>{z|I.constantHull.Contains z})
      (DomainConstraints.exactDomain Cube) :=
  ⟨fun _=>⟨id,id⟩,fun _ ht _ hz=>demotion_encloses I ht hz⟩

noncomputable def fromAffine {n} (I : MultiAffineFamilies.Bounds n) : Bounds n :=
  ⟨embed I.lower,embed I.upper,by
    intro t ht; rw [embed_value,embed_value]; exact bounds_ordered I ht⟩
theorem fromAffine_contains {n} (I : MultiAffineFamilies.Bounds n) (t) (z) :
    (fromAffine I).Contains t z ↔ I.Contains t z := by
  simp [Bounds.Contains,fromAffine,embed_value,MultiAffineFamilies.Bounds.Contains]

/-- Reuse the already proved one-parameter chord correction for products. -/
theorem product_chord_demotion (a b : QAffine) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (a.productBounds b).Contains t
      ((product (fromQAffine a) (fromQAffine b)).value (fun _=>t)) := by
  rw [product_value,fromQAffine_value,fromQAffine_value]
  exact affine_product_encloses a b ht

end GeneralizedIntervalArithmetic.QuadraticFamilies
