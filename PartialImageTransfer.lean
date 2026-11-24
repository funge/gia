import GeneralFamilyDemotion
import RootTransfer
import PartialRealArithmetic

/-! Exact transfer through injective partial real operations. The image reuses
`GeneralFamilyDemotion.outputs`; finite certificates check domains, not geometry. -/
namespace GeneralizedIntervalArithmetic.PartialImageTransfer

abbrev image (R : ℝ → ℝ → Prop) (S : Set ℝ) : Set ℝ :=
  GeneralFamilyDemotion.outputs (fun (_ : Unit) x => x ∈ S) (fun _ => R) ()

def Defined (R : ℝ → ℝ → Prop) (x : ℝ) : Prop := ∃ z, R x z

def Injective (R : ℝ → ℝ → Prop) : Prop :=
  ∀ x y z, R x z → R y z → x = y

theorem image_mono {R : ℝ → ℝ → Prop} {S T : Set ℝ} (h : S ⊆ T) :
    image R S ⊆ image R T := by
  rintro z ⟨x,hx,hz⟩
  exact ⟨x,h hx,hz⟩

/-- Sufficiency needs no injectivity or totality. Every newly admitted point
must be outside the operation domain. -/
theorem exact_of_domain {R : ℝ → ℝ → Prop} {S T : Set ℝ} (h : S ⊆ T)
    (hd : ∀ x ∈ T, Defined R x → x ∈ S) : image R T = image R S := by
  apply Set.Subset.antisymm _ (image_mono h)
  rintro z ⟨x,hx,hz⟩
  exact ⟨x,hd x hx ⟨z,hz⟩,hz⟩

/-- With an injective graph, absence of new defined inputs is also necessary. -/
theorem exact_iff {R : ℝ → ℝ → Prop} (hi : Injective R)
    {S T : Set ℝ} (h : S ⊆ T) :
    image R T = image R S ↔ ∀ x ∈ T, Defined R x → x ∈ S := by
  refine ⟨?_,exact_of_domain h⟩
  rintro he x hx ⟨z,hz⟩
  have hm : z ∈ image R T := ⟨x,hx,hz⟩
  rw [he] at hm
  obtain ⟨y,hy,hyz⟩ := hm
  simpa [hi x y z hz hyz] using hy

/-- Exactness preserves the actual defined-input subset, not all input flags. -/
theorem exact_iff_domain_intersection {R : ℝ → ℝ → Prop} (hi : Injective R)
    {S T : Set ℝ} (h : S ⊆ T) :
    image R T = image R S ↔ T ∩ {x | Defined R x} = S ∩ {x | Defined R x} := by
  rw [exact_iff hi h]
  constructor
  · intro hd
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨hd x hx.1 hx.2,hx.2⟩
    · intro x hx
      exact ⟨h hx.1,hx.2⟩
  · intro he x hx hd
    have hm : x ∈ T ∩ {x | Defined R x} := ⟨hx,hd⟩
    rw [he] at hm
    exact hm.1

/-- Executable on decidable labels (e.g. rationals). Geometry and the domain
interpretation of those labels remain separate proved obligations. -/
def blocked? {ι : Type*} (E : Finset ι) (p : ι → Prop) [DecidablePred p] : Bool :=
  decide (∀ i ∈ E, ¬ p i)

theorem blocked_iff {ι : Type*} (E : Finset ι) (p : ι → Prop) [DecidablePred p] :
    blocked? E p = true ↔ ∀ i ∈ E, ¬ p i := by simp [blocked?]

theorem exact_of_finite_gaps {ι : Type*} {R : ℝ → ℝ → Prop} {S T : Set ℝ}
    (h : S ⊆ T) (E : Finset ι) (g : ι → ℝ) (p : ι → Prop) [DecidablePred p]
    (cover : ∀ x ∈ T, x ∈ S ∨ ∃ i ∈ E, x = g i)
    (domain : ∀ i ∈ E, Defined R (g i) ↔ p i)
    (check : blocked? E p = true) : image R T = image R S := by
  apply exact_of_domain h
  intro x hx hd
  rcases cover x hx with hs | ⟨i,hi,rfl⟩
  · exact hs
  · exact False.elim ((blocked_iff E p).mp check i hi ((domain i hi).mp hd))

def root (x z : ℝ) : Prop := 0 ≤ x ∧ z = Real.sqrt x

theorem root_image (S : Set ℝ) : image root S = RootTransfer.roots S := by
  ext z
  rfl

theorem root_domain (x : ℝ) : Defined root x ↔ 0 ≤ x := by
  exact ⟨fun ⟨_,h,_⟩ => h, fun h => ⟨Real.sqrt x,h,rfl⟩⟩

theorem root_injective : Injective root := by
  rintro x y z ⟨hx,hxz⟩ ⟨hy,hyz⟩
  have he : Real.sqrt x = Real.sqrt y := hxz.symm.trans hyz
  have := congrArg (fun r : ℝ => r^2) he
  simpa [Real.sq_sqrt hx,Real.sq_sqrt hy] using this

abbrev reciprocal := PartialRealArithmetic.divRel 1

theorem reciprocal_domain (x : ℝ) : Defined reciprocal x ↔ x ≠ 0 := by
  exact ⟨fun ⟨_,h,_⟩ => h, fun h => ⟨1/x,h,rfl⟩⟩

theorem reciprocal_injective : Injective reciprocal := by
  rintro x y z ⟨_,hx⟩ ⟨_,hy⟩
  exact inv_injective (by simpa only [one_div] using hx.symm.trans hy)

/-- Closing the zero hole adds no reciprocal value; other missing nonzero
points do matter, including missing closed boundary points. -/
theorem reciprocal_exact_iff {S T : Set ℝ} (h : S ⊆ T) :
    image reciprocal T = image reciprocal S ↔ ∀ x ∈ T, x ≠ 0 → x ∈ S := by
  simpa only [reciprocal_domain] using exact_iff reciprocal_injective h

theorem reciprocal_remove_zero (T : Set ℝ) :
    image reciprocal T = image reciprocal (T \ {0}) := by
  apply (reciprocal_exact_iff Set.diff_subset).2
  intro x hx hn
  exact ⟨hx,hn⟩
/-- Exact output transfer preserves existence of a defined input. It does not
preserve the universal-definedness classification of a widened input set. -/
theorem possible_iff {R : ℝ → ℝ → Prop} {S T : Set ℝ}
    (h : image R T = image R S) :
    (∃ x ∈ T, Defined R x) ↔ ∃ x ∈ S, Defined R x := by
  constructor
  · rintro ⟨x,hx,z,hz⟩
    have hm : z ∈ image R T := ⟨x,hx,hz⟩
    rw [h] at hm
    obtain ⟨y,hy,hyz⟩ := hm
    exact ⟨y,hy,z,hyz⟩
  · rintro ⟨x,hx,z,hz⟩
    have hm : z ∈ image R S := ⟨x,hx,hz⟩
    rw [← h] at hm
    obtain ⟨y,hy,hyz⟩ := hm
    exact ⟨y,hy,z,hyz⟩
end GeneralizedIntervalArithmetic.PartialImageTransfer
