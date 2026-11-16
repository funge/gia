import HardwareEvaluatorProgram
import HardwareAffineProduct
import HardwareCover

namespace GeneralizedIntervalArithmetic.HardwareEvaluator
open HardwareAddition

/-- A constant has a value only when its backend interpretation supplies one.
All input occurrences denote the same real input. No division is present. -/
inductive Value {C : Type} (decode : C → Option ℝ) (x : ℝ) : Polynomial C → ℝ → Prop where
  | const {c v} : decode c = some v → Value decode x (.const c) v
  | var : Value decode x .var x
  | add {a b u v} : Value decode x a u → Value decode x b v → Value decode x (.add a b) (u+v)
  | sub {a b u v} : Value decode x a u → Value decode x b v → Value decode x (.sub a b) (u-v)
  | mul {a b u v} : Value decode x a u → Value decode x b v → Value decode x (.mul a b) (u*v)

/-- Representation-independent compositional enclosure for the shared traversal. -/
theorem eval_sound {C A : Type} {decode : C → Option ℝ} {R : A → ℝ → Prop}
    {constant : C → Option A} {input : Option A} {add sub mul : A → A → Option A}
    (hc : ∀ c a v, constant c = some a → decode c = some v → R a v)
    {x : ℝ} (hv : ∀ a, input = some a → R a x)
    (ha : ∀ a b o u v, add a b = some o → R a u → R b v → R o (u+v))
    (hs : ∀ a b o u v, sub a b = some o → R a u → R b v → R o (u-v))
    (hm : ∀ a b o u v, mul a b = some o → R a u → R b v → R o (u*v))
    {e : Polynomial C} {v : ℝ} (he : Value decode x e v) {o : A}
    (hr : eval (m := Id) constant input add sub mul e = some o) : R o v := by
  induction he generalizing o with
  | const h => exact hc _ _ _ hr h
  | var => exact hv _ hr
  | add h1 h2 ih1 ih2 =>
    simp only [eval,bind,pure] at hr
    split at hr <;> try contradiction
    next a hA =>
      split at hr <;> try contradiction
      next b hB => exact ha _ _ _ _ _ hr (ih1 hA) (ih2 hB)
  | sub h1 h2 ih1 ih2 =>
    simp only [eval,bind,pure] at hr
    split at hr <;> try contradiction
    next a hA =>
      split at hr <;> try contradiction
      next b hB => exact hs _ _ _ _ _ hr (ih1 hA) (ih2 hB)
  | mul h1 h2 ih1 ih2 =>
    simp only [eval,bind,pure] at hr
    split at hr <;> try contradiction
    next a hA =>
      split at hr <;> try contradiction
      next b hB => exact hm _ _ _ _ _ hr (ih1 hA) (ih2 hB)

theorem ordinary_eval_sound {C F : Type} {constantDecode : C → Option ℝ}
    {decode : F → Option ℝ} {constant : C → Option (Bounds F)}
    {input : Option (Bounds F)} {add sub mul : Bounds F → Bounds F → Option (Bounds F)}
    (hc : ∀ c I v, constant c = some I → constantDecode c = some v → Contains decode I v)
    {x : ℝ} (hv : ∀ I, input = some I → Contains decode I x)
    (ha : HardwareIntervalOps.OpSound decode add (· + ·))
    (hs : HardwareIntervalOps.OpSound decode sub (· - ·))
    (hm : HardwareIntervalOps.OpSound decode mul (· * ·))
    {e : Polynomial C} {v : ℝ} (he : Value constantDecode x e v) {O : Bounds F}
    (hr : eval (m := Id) constant input add sub mul e = some O) : Contains decode O v :=
  eval_sound hc hv ha hs hm he hr

theorem affine_eval_sound {C F : Type} {constantDecode : C → Option ℝ}
    {decode : F → Option ℝ} {constant : C → Option (HardwareAffine.Form F)}
    {input : Option (HardwareAffine.Form F)}
    {add sub mul : Bounds F → Bounds F → Option (Bounds F)}
    {bubble : Bounds F} {t x : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hb : ∀ u ∈ Set.Icc (0:ℝ) (1/4), Contains decode bubble u)
    (hc : ∀ c I v, constant c = some I → constantDecode c = some v → HardwareAffine.Contains decode I t v)
    (hv : ∀ I, input = some I → HardwareAffine.Contains decode I t x)
    (ha : HardwareIntervalOps.OpSound decode add (· + ·))
    (hs : HardwareIntervalOps.OpSound decode sub (· - ·))
    (hm : HardwareIntervalOps.OpSound decode mul (· * ·))
    {e : Polynomial C} {v : ℝ} (he : Value constantDecode x e v) {O : HardwareAffine.Form F}
    (hr : affineEval (m := Id) constant input add sub mul bubble e = some O) :
    HardwareAffine.Contains decode O t v := by
  exact eval_sound hc hv
    (fun _ _ _ _ _ hr hx hy => HardwareAffine.add_sound ha hr hx hy)
    (fun _ _ _ _ _ hr hx hy => HardwareAffine.sub_sound hs hr hx hy)
    (fun _ _ _ _ _ hr hx hy => HardwareAffine.product_sound hs hm hb ht hr hx hy) he hr

/-- Lifting a sound constant interval to a constant form needs no new contract. -/
theorem constant_form_sound {F : Type} {decode : F → Option ℝ} {I : Bounds F}
    {v t : ℝ} (hc : Contains decode I v) :
    HardwareAffine.Contains decode ⟨I,I⟩ t v := ⟨v,v,hc,hc,by ring⟩

theorem seed_sound {F : Type} {decode : F → Option ℝ} {I : Bounds F} {l u t : ℝ}
    (hl : decode I.lo = some l) (hu : decode I.hi = some u) (hlu : l ≤ u)
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    Contains decode I ((1-t)*l+t*u) ∧ HardwareAffine.Contains decode (seed I) t ((1-t)*l+t*u) := by
  constructor
  · exact ⟨l,u,hl,hu,HardwareAffine.weighted_bounds (sub_nonneg.mpr ht.2) ht.1 (by ring)
      ⟨le_rfl,hlu⟩ ⟨hlu,le_rfl⟩⟩
  · exact ⟨l,u,⟨l,l,hl,hl,le_rfl,le_rfl⟩,⟨u,u,hu,hu,le_rfl,le_rfl⟩,rfl⟩

/-- Every represented ordinary input has a shared-parameter seed witness,
including degenerate intervals. No division by the interval width is needed. -/
theorem seed_covers {F : Type} {decode : F → Option ℝ} {I : Bounds F} {x : ℝ}
    (hx : Contains decode I x) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, HardwareAffine.Contains decode (seed I) t x := by
  rcases hx with ⟨l,u,hl,hu,hlx,hxu⟩
  obtain ⟨a,b,ha,hb,hab,he⟩ := (Convex.mem_Icc (hlx.trans hxu)).mp ⟨hlx,hxu⟩
  have ht : b ∈ Set.Icc (0:ℝ) 1 := ⟨hb,by linarith⟩
  refine ⟨b,ht,?_⟩
  have hs := (seed_sound hl hu (hlx.trans hxu) ht).2
  have hab' : 1-b = a := by linarith
  have hx' : (1-b)*l+b*u = x := by simpa [hab'] using he
  rw [hx'] at hs
  exact hs

theorem merge_sound {F : Type} {decode : F → Option ℝ}
    {lt : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {I J : Option (Bounds F)} {v : ℝ}
    (hi : ∀ a, I = some a → Contains decode a v)
    (hj : ∀ a, J = some a → Contains decode a v)
    {O : Bounds F} (hr : merge lt mn mx I J = .bound O) : Contains decode O v := by
  cases I with
  | none => cases J with
    | none => simp [merge] at hr
    | some J => cases hr; exact hj _ rfl
  | some I => cases J with
    | none => cases hr; exact hi _ rfl
    | some J =>
      obtain ⟨K,hK,hv⟩ := HardwareQuadrants.clip_point hc hn hm (hi I rfl) (hj J rfl)
      simp [merge,hK] at hr
      subst O; exact hv

/-- A successful ordinary track survives and bounds the combined result, under
common-value contracts. This includes both availability and non-widening. -/
theorem ordinary_survives {F : Type} {decode : F → Option ℝ}
    {lt : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {I : Bounds F} {J : Option (Bounds F)} {v : ℝ}
    (hi : Contains decode I v) (hj : ∀ a, J = some a → Contains decode a v) :
    ∃ O, merge lt mn mx (some I) J = .bound O ∧ Contains decode O v ∧
      ∀ z, Contains decode O z → Contains decode I z := by
  cases J with
  | none => exact ⟨I,rfl,hi,fun _ h => h⟩
  | some J =>
    have hj' := hj J rfl
    obtain ⟨K,hK,hv⟩ := HardwareQuadrants.clip_point hc hn hm hi hj'
    refine ⟨K,by simp [merge,hK],hv,?_⟩
    intro z hz
    exact (HardwareQuadrants.clip_subset hn hm
      (HardwareQuadrants.valid_of_contains hi) (HardwareQuadrants.valid_of_contains hj') hK hz).1

/-- Contradictory tracks cannot arise when both contracts enclose a common value. -/
theorem merge_no_conflict {F : Type} {decode : F → Option ℝ}
    {lt : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {I J : Option (Bounds F)} {v : ℝ}
    (hi : ∀ a, I = some a → Contains decode a v)
    (hj : ∀ a, J = some a → Contains decode a v) : merge lt mn mx I J ≠ .conflict := by
  cases I with
  | none => cases J <;> simp [merge]
  | some I =>
    obtain ⟨O,hO,_,_⟩ := ordinary_survives hc hn hm (hi I rfl) hj
    rw [hO]; intro h; cases h

theorem run_sound {C F : Type} {decode : F → Option ℝ}
    {ordinary : Polynomial C → Option (Bounds F)}
    {affine : Polynomial C → Option (HardwareAffine.Form F)}
    {lt : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {e : Polynomial C} {t v : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (ho : ∀ O, ordinary e = some O → Contains decode O v)
    (ha : ∀ A, affine e = some A → HardwareAffine.Contains decode A t v)
    {O : Bounds F} (hr : run (m := Id) ordinary affine lt mn mx e = .bound O) :
    Contains decode O v := by
  apply merge_sound hc hn hm ho _ hr
  intro J hJ
  cases hA : affine e with
  | none => simp [hA] at hJ
  | some A =>
    simp [hA] at hJ
    subst J
    exact HardwareAffine.hull_sound hn hm ht (ha A hA)

/-- Whole-program ordinary-track survival and semantic non-widening. -/
theorem run_ordinary_survives {C F : Type} {decode : F → Option ℝ}
    {ordinary : Polynomial C → Option (Bounds F)}
    {affine : Polynomial C → Option (HardwareAffine.Form F)}
    {lt : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {e : Polynomial C} {t v : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    {I : Bounds F} (hi : ordinary e = some I) (hv : Contains decode I v)
    (ha : ∀ A, affine e = some A → HardwareAffine.Contains decode A t v) :
    ∃ O, run (m := Id) ordinary affine lt mn mx e = .bound O ∧ Contains decode O v ∧
      ∀ z, Contains decode O z → Contains decode I z := by
  have hj : ∀ J, (affine e).map (HardwareAffine.hull mn mx) = some J → Contains decode J v := by
    intro J hJ
    cases hA : affine e with
    | none => simp [hA] at hJ
    | some A =>
      simp [hA] at hJ
      subst J
      exact HardwareAffine.hull_sound hn hm ht (ha A hA)
  obtain ⟨O,hO,hv',hsub⟩ := ordinary_survives hc hn hm hv hj
  exact ⟨O,by simpa [run,hi] using hO,hv',hsub⟩

end GeneralizedIntervalArithmetic.HardwareEvaluator
