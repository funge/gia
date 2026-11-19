import PartialRealArithmetic
import HardwareQuotientProgram
import HardwareEvaluator

namespace GeneralizedIntervalArithmetic.HardwareQuotient
open HardwareAddition HardwareEvaluator

noncomputable def meaning : Operation → ℝ → ℝ → ℝ
  | .add => PartialRealArithmetic.add
  | .sub => PartialRealArithmetic.sub
  | .mul => PartialRealArithmetic.mul
  | .div => PartialRealArithmetic.div

def Defined : Operation → ℝ → ℝ → Prop
  | .div => PartialRealArithmetic.divDefined
  | _ => PartialRealArithmetic.totalDefined

inductive Value {C : Type} (decode : C → Option ℝ) (x : ℝ) : Expression C → ℝ → Prop where
  | polynomial {p v} : HardwareEvaluator.Value decode x p v → Value decode x (.polynomial p) v
  | binary {k a b u v} : Value decode x a u → Value decode x b v → Defined k u v →
      Value decode x (.binary k a b) (meaning k u v)

theorem polynomial_unique {C : Type} {decode : C → Option ℝ} {x : ℝ}
    {p : Polynomial C} {u v : ℝ} (hu : HardwareEvaluator.Value decode x p u)
    (hv : HardwareEvaluator.Value decode x p v) : u=v := by
  induction hu generalizing v with
  | const h => cases hv with | const h' => exact Option.some.inj (h.symm.trans h')
  | var => cases hv; rfl
  | add h1 h2 ih1 ih2 => cases hv with | add h1' h2' => rw [ih1 h1',ih2 h2']
  | sub h1 h2 ih1 ih2 => cases hv with | sub h1' h2' => rw [ih1 h1',ih2 h2']
  | mul h1 h2 ih1 ih2 => cases hv with | mul h1' h2' => rw [ih1 h1',ih2 h2']

theorem value_unique {C : Type} {decode : C → Option ℝ} {x : ℝ}
    {e : Expression C} {u v : ℝ} (hu : Value decode x e u) (hv : Value decode x e v) : u=v := by
  induction hu generalizing v with
  | polynomial h => cases hv with | polynomial h' => exact polynomial_unique h h'
  | binary h1 h2 hd ih1 ih2 =>
    cases hv with | binary h1' h2' hd' => rw [ih1 h1',ih2 h2']

/-- Existing guarded quotient assembly discharges the division instance; this
contract explicitly includes definedness, not merely totalized real division. -/
def OperationSound {F : Type} (decode : F → Option ℝ) (k : Operation)
    (op : Bounds F → Bounds F → Option (Bounds F)) : Prop :=
  ∀ I J O x y, op I J = some O → Contains decode I x → Contains decode J y →
    Contains decode O (meaning k x y) ∧ Defined k x y

def Cert {F : Type} (decode : F → Option ℝ) (R : ℝ → Prop) (I : Option (Bounds F)) : Prop :=
  ∀ B, I = some B → ∃ v, R v ∧ Contains decode B v

def ResultCert {F : Type} (decode : F → Option ℝ) (R : ℝ → Prop) (out : Result F) : Prop :=
  out ≠ .conflict ∧ ∀ B, out = .bound B → ∃ v, R v ∧ Contains decode B v

def Certified {C F : Type} (cd : C → Option ℝ) (decode : F → Option ℝ) (x : ℝ)
    (e : Expression C) (out : Tracks F) : Prop :=
  Cert decode (Value cd x e) out.ordinary ∧ ResultCert decode (Value cd x e) out.refined

theorem merge_cert {F : Type} {decode : F → Option ℝ} {R : ℝ → Prop}
    (unique : ∀ u v, R u → R v → u=v)
    {lt : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {I J : Option (Bounds F)} (hi : Cert decode R I) (hj : Cert decode R J) :
    ResultCert decode R (merge lt mn mx I J) := by
  cases I with
  | none =>
    cases J with
    | none => simp [ResultCert,merge]
    | some J =>
      refine ⟨by simp [merge],?_⟩
      intro B hB
      cases hB
      exact hj _ rfl
  | some I =>
    obtain ⟨v,hv,hIv⟩ := hi I rfl
    have hI : ∀ B, some I = some B → Contains decode B v := by intro B h; cases h; exact hIv
    have hJ : ∀ B, J = some B → Contains decode B v := by
      intro B h
      obtain ⟨w,hw,hBw⟩ := hj B h
      rw [unique w v hw hv] at hBw
      exact hBw
    exact ⟨merge_no_conflict hc hn hm hI hJ,
      fun B hB => ⟨v,hv,merge_sound hc hn hm hI hJ hB⟩⟩

theorem available_cert {F : Type} {decode : F → Option ℝ} {R : ℝ → Prop}
    {out : Result F} (h : ResultCert decode R out) : Cert decode R (available out) := by
  intro B hB
  cases out with
  | unknown => simp [available] at hB
  | conflict => exact False.elim (h.1 rfl)
  | bound A => cases hB; exact h.2 _ rfl

theorem attempt_cert {C F : Type} {cd : C → Option ℝ} {decode : F → Option ℝ} {x : ℝ}
    {k : Operation} {op : Bounds F → Bounds F → Option (Bounds F)}
    (hop : OperationSound decode k op) {a b : Expression C} {I J : Option (Bounds F)}
    (hi : Cert decode (Value cd x a) I) (hj : Cert decode (Value cd x b) J) :
    Cert decode (Value cd x (.binary k a b)) (attempt (m := Id) op I J) := by
  intro O hO
  cases I with
  | none => simp [attempt] at hO
  | some I => cases J with
    | none => simp [attempt] at hO
    | some J =>
      obtain ⟨u,hu,hI⟩ := hi I rfl
      obtain ⟨v,hv,hJ⟩ := hj J rfl
      obtain ⟨hB,hd⟩ := hop I J O u v hO hI hJ
      exact ⟨meaning k u v,Value.binary hu hv hd,hB⟩

theorem step_cert {C F : Type} {cd : C → Option ℝ} {decode : F → Option ℝ} {x : ℝ}
    {k : Operation} {op : Bounds F → Bounds F → Option (Bounds F)}
    (hop : OperationSound decode k op) {lt : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {a b : Expression C} {I J : Tracks F}
    (hi : Certified cd decode x a I) (hj : Certified cd decode x b J) :
    Certified cd decode x (.binary k a b) (step (m := Id) op lt mn mx I J) := by
  have ho := attempt_cert hop hi.1 hj.1
  have hr := attempt_cert hop (available_cert hi.2) (available_cert hj.2)
  have hmerge := merge_cert (fun _ _ => value_unique) hc hn hm ho hr
  cases hI : I.refined <;> cases hJ : J.refined
  all_goals try { exact False.elim (hi.2.1 hI) }
  all_goals try { exact False.elim (hj.2.1 hJ) }
  all_goals exact ⟨by simpa [step,hI,hJ] using ho,by simpa [step,hI,hJ] using hmerge⟩

/-- Only leaves actually present in this expression require certificates. -/
def AllLeaves {C : Type} (P : Polynomial C → Prop) : Expression C → Prop
  | .polynomial p => P p
  | .binary _ a b => AllLeaves P a ∧ AllLeaves P b

theorem eval_cert {C F : Type} {cd : C → Option ℝ} {decode : F → Option ℝ} {x : ℝ}
    {leaf : Polynomial C → Tracks F}
    {op : Operation → Bounds F → Bounds F → Option (Bounds F)}
    (hop : ∀ k, OperationSound decode k (op k))
    {lt : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max) (e : Expression C)
    (hl : AllLeaves (fun p => Certified cd decode x (.polynomial p) (leaf p)) e) :
    Certified cd decode x e (eval (m := Id) leaf op lt mn mx e) := by
  induction e with
  | polynomial p => exact hl
  | binary k a b ihA ihB => exact step_cert (hop k) hc hn hm (ihA hl.1) (ihB hl.2)

/-- This is exactly the previously approved finite guarded division assembly. -/
theorem guarded_division_sound {F : Type} {decode : F → Option ℝ}
    {call : F → F → Option (F × F)} {lt : F → F → Bool} {mn mx : F → F → F}
    {zero : F} (hz : decode zero = some 0)
    (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    (hd : ∀ a b, HardwareDivision.CallSound decode a b (call a b)) :
    OperationSound decode .div (fun I J => HardwareDivision.assembleGuarded lt zero mn mx J
      (call I.lo J.lo) (call I.lo J.hi) (call I.hi J.lo) (call I.hi J.hi)) := by
  intro I J O x y hr hx hy
  exact HardwareDivision.assembleGuarded_encloses hc hz hn hm
    (hd _ _) (hd _ _) (hd _ _) (hd _ _) hr hx hy

theorem add_sound {F : Type} {decode : F → Option ℝ}
    {op : Bounds F → Bounds F → Option (Bounds F)}
    (h : HardwareIntervalOps.OpSound decode op (· + ·)) : OperationSound decode .add op :=
  fun _ _ _ _ _ hr hx hy => ⟨h _ _ _ _ _ hr hx hy,True.intro⟩

theorem sub_sound {F : Type} {decode : F → Option ℝ}
    {op : Bounds F → Bounds F → Option (Bounds F)}
    (h : HardwareIntervalOps.OpSound decode op (· - ·)) : OperationSound decode .sub op :=
  fun _ _ _ _ _ hr hx hy => ⟨h _ _ _ _ _ hr hx hy,True.intro⟩

theorem mul_sound {F : Type} {decode : F → Option ℝ}
    {op : Bounds F → Bounds F → Option (Bounds F)}
    (h : HardwareIntervalOps.OpSound decode op (· * ·)) : OperationSound decode .mul op :=
  fun _ _ _ _ _ hr hx hy => ⟨h _ _ _ _ _ hr hx hy,True.intro⟩

def NoWiden {F : Type} (decode : F → Option ℝ) (out : Tracks F) : Prop :=
  ∀ I, out.ordinary = some I → ∃ O, out.refined = .bound O ∧
    ∀ z, Contains decode O z → Contains decode I z

theorem merge_preserves {F : Type} {decode : F → Option ℝ} {R : ℝ → Prop}
    (unique : ∀ u v, R u → R v → u=v)
    {lt : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {I J : Option (Bounds F)} (hi : Cert decode R I) (hj : Cert decode R J) :
    NoWiden decode ⟨I,merge lt mn mx I J⟩ := by
  intro B hB
  change I = some B at hB
  obtain ⟨v,hv,hIv⟩ := hi B hB
  have hJ : ∀ A, J = some A → Contains decode A v := by
    intro A hA
    obtain ⟨w,hw,hAw⟩ := hj A hA
    rw [unique w v hw hv] at hAw
    exact hAw
  obtain ⟨O,hO,_,hs⟩ := ordinary_survives hc hn hm hIv hJ
  exact ⟨O,by simpa [hB] using hO,hs⟩

theorem step_preserves {C F : Type} {cd : C → Option ℝ} {decode : F → Option ℝ} {x : ℝ}
    {k : Operation} {op : Bounds F → Bounds F → Option (Bounds F)}
    (hop : OperationSound decode k op) {lt : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max)
    {a b : Expression C} {I J : Tracks F}
    (hi : Certified cd decode x a I) (hj : Certified cd decode x b J) :
    NoWiden decode (step (m := Id) op lt mn mx I J) := by
  have h := merge_preserves (fun _ _ => value_unique) hc hn hm
    (attempt_cert hop hi.1 hj.1) (attempt_cert hop (available_cert hi.2) (available_cert hj.2))
  cases hI : I.refined <;> cases hJ : J.refined
  all_goals try { exact False.elim (hi.2.1 hI) }
  all_goals try { exact False.elim (hj.2.1 hJ) }
  all_goals simpa [step,hI,hJ] using h

theorem eval_preserves {C F : Type} {cd : C → Option ℝ} {decode : F → Option ℝ} {x : ℝ}
    {leaf : Polynomial C → Tracks F}
    {op : Operation → Bounds F → Bounds F → Option (Bounds F)}
    (hop : ∀ k, OperationSound decode k (op k))
    {lt : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max) (e : Expression C)
    (hl : AllLeaves (fun p => Certified cd decode x (.polynomial p) (leaf p)) e)
    (hw : AllLeaves (fun p => NoWiden decode (leaf p)) e) :
    NoWiden decode (eval (m := Id) leaf op lt mn mx e) := by
  cases e with
  | polynomial p => exact hw
  | binary k a b =>
    exact step_preserves (hop k) hc hn hm
      (eval_cert hop hc hn hm a hl.1) (eval_cert hop hc hn hm b hl.2)

/-- Earlier polynomial enclosure proofs discharge leaf certificates for every
real point with an interpreted polynomial value; this is not an FP axiom. -/
theorem polynomial_leaf_cert {C F : Type} {cd : C → Option ℝ} {decode : F → Option ℝ}
    {x t v : ℝ} {p : Polynomial C} (hv : HardwareEvaluator.Value cd x p v)
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    {I : Option (Bounds F)} {A : Option (HardwareAffine.Form F)}
    (hi : ∀ O, I = some O → Contains decode O v)
    (ha : ∀ O, A = some O → HardwareAffine.Contains decode O t v)
    {lt : F → F → Bool} {mn mx : F → F → F}
    (hc : HardwareDivision.CompareSound decode lt)
    (hn : HardwareMultiplication.SelectSound decode mn min)
    (hm : HardwareMultiplication.SelectSound decode mx max) :
    Certified cd decode x (.polynomial p) (polynomialTracks lt mn mx I A) ∧
    NoWiden decode (polynomialTracks lt mn mx I A) := by
  have hI : Cert decode (Value cd x (.polynomial p)) I :=
    fun O hO => ⟨v,Value.polynomial hv,hi O hO⟩
  have hA : Cert decode (Value cd x (.polynomial p)) (A.map (HardwareAffine.hull mn mx)) := by
    intro B hB
    cases he : A with
    | none => simp [he] at hB
    | some A =>
      simp [he] at hB
      subst B
      exact ⟨v,Value.polynomial hv,HardwareAffine.hull_sound hn hm ht (ha A he)⟩
  exact ⟨⟨hI,merge_cert (fun _ _ => value_unique) hc hn hm hI hA⟩,
    merge_preserves (fun _ _ => value_unique) hc hn hm hI hA⟩

/-- Successful returned bounds certify a defined value, not just a totalized quotient. -/
theorem success_defined {C F : Type} {cd : C → Option ℝ} {decode : F → Option ℝ}
    {x : ℝ} {e : Expression C} {out : Tracks F} (h : Certified cd decode x e out)
    {O : Bounds F} (hr : out.refined = .bound O) :
    ∃ v, Value cd x e v ∧ Contains decode O v := h.2.2 O hr

end GeneralizedIntervalArithmetic.HardwareQuotient
