import PieceDomainConversion
import GuardedEvaluator

/-! Compose generated domain descriptions with the existing guarded evaluator.
Success keeps the same parameter and coordinate-choice witness; failure is unknown. -/
namespace GeneralizedIntervalArithmetic.GuardedPieceComposition
open FiniteGuardPieces MixedEndpoints PieceDomainConversion

/-- Construct the existing finite affine interval only if its endpoint order
holds on the whole unit parameter interval. -/
def bounds? (b : Band) : Option LinearInterval :=
  if h0 : b.lower.atZero ≤ b.upper.atZero then
    if h1 : b.lower.atOne ≤ b.upper.atOne then
      some ⟨b.lower,b.upper,h0,h1⟩ else none
  else none

theorem bounds_enclose {b : Band} {I : LinearInterval} (h : bounds? b = some I)
    {t x : ℝ} (hx : x ∈ b.denote t) : I.Contains t x := by
  unfold bounds? at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases Option.some.inj h
  change b.lower.value t ≤ x ∧ x ≤ b.upper.value t
  rw [lower_value,upper_value]
  have hc := (converted_exact b t x).1 (converted_encloses b t hx)
  exact hc.1

def unitGuard : Guard := [(⟨0,-1⟩,false),(⟨-1,0⟩,false)]

theorem unit_guard_exact (t : ℝ) : guardHolds unitGuard t ↔ t ∈ Set.Icc (0:ℝ) 1 := by
  simp [unitGuard,guardHolds,QAffine.value]

theorem guard_append (g h : Guard) (t : ℝ) :
    guardHolds (g++h) t ↔ guardHolds g t ∧ guardHolds h t := by
  simp [guardHolds,List.mem_append,or_imp,forall_and]

def inputGuard (b c : Band) : Guard := unitGuard ++ activeGuard b ++ activeGuard c

theorem input_guard_exact (b c : Band) (t : ℝ) :
    guardHolds (inputGuard b c) t ↔
      t ∈ Set.Icc (0:ℝ) 1 ∧ (b.denote t).Nonempty ∧ (c.denote t).Nonempty := by
  simp only [inputGuard,guard_append,unit_guard_exact,active_iff,and_assoc]

structure Result where
  values : LinearInterval
  domain : Guard

def evaluate? (b c : Band) (e : Expr) : Option Result := do
  let X ← bounds? b
  let Y ← bounds? c
  let R ← evalGuarded X Y e
  pure ⟨R,inputGuard b c⟩

theorem evaluate_parts {b c : Band} {e : Expr} {r : Result}
    (h : evaluate? b c e = some r) :
    ∃ X Y, bounds? b = some X ∧ bounds? c = some Y ∧
      evalGuarded X Y e = some r.values ∧ r.domain = inputGuard b c := by
  unfold evaluate? at h
  cases hb : bounds? b with
  | none => simp [hb] at h
  | some X =>
    cases hc : bounds? c with
    | none => simp [hb,hc] at h
    | some Y =>
      cases he : evalGuarded X Y e with
      | none => simp [hb,hc,he] at h
      | some R =>
        have hr : Result.mk R (inputGuard b c) = r := by simpa [hb,hc,he] using h
        cases hr
        exact ⟨X,Y,rfl,rfl,he,rfl⟩

/-- Strict coordinate environment: both bands must supply actual coordinates,
even if an expression does not mention one. All occurrences reuse that pair. -/
def Values (b c : Band) (e : Expr) (t z : ℝ) : Prop :=
  t ∈ Set.Icc (0:ℝ) 1 ∧ ∃ x y, x ∈ b.denote t ∧ y ∈ c.denote t ∧ Value x y e z

theorem evaluate_encloses {b c : Band} {e : Expr} {r : Result}
    (h : evaluate? b c e = some r) {t z : ℝ} (hv : Values b c e t z) :
    r.values.Contains t z := by
  obtain ⟨X,Y,hx,hy,he,_⟩ := evaluate_parts h
  obtain ⟨ht,x,y,hbx,hcy,hv⟩ := hv
  exact evalGuarded_sound ht (bounds_enclose hx hbx) (bounds_enclose hy hcy) hv he

/-- The successful guarded evaluator discharges the operation-domain premise.
It is not inferred merely from nonempty input enclosures. -/
theorem evaluate_domain_exact {b c : Band} {e : Expr} {r : Result}
    (h : evaluate? b c e = some r) (t : ℝ) :
    guardHolds r.domain t ↔ ∃ z, Values b c e t z := by
  obtain ⟨X,Y,hx,hy,he,hd⟩ := evaluate_parts h
  rw [hd,input_guard_exact]
  constructor
  · rintro ⟨ht,⟨x,hbx⟩,⟨y,hcy⟩⟩
    obtain ⟨z,hz⟩ := evalGuarded_defined ht (bounds_enclose hx hbx) (bounds_enclose hy hcy) he
    exact ⟨z,ht,x,y,hbx,hcy,hz⟩
  · rintro ⟨z,ht,x,y,hbx,hcy,_⟩
    exact ⟨ht,⟨x,hbx⟩,⟨y,hcy⟩⟩

def domainCode (r : Result) : Description := .cell (guardAtoms r.domain)
def admitted? (r : Result) (t : ℚ) : Bool := test (domainCode r).compile t 0

theorem admitted_exact {b c : Band} {e : Expr} {r : Result}
    (h : evaluate? b c e = some r) (t : ℚ) :
    admitted? r t = true ↔ ∃ z, Values b c e (t:ℝ) z := by
  rw [admitted?,compiled_test_exact]
  simpa only [Rat.cast_zero,domainCode,Description.denote] using
    (guard_exact r.domain (t:ℝ) 0).trans (evaluate_domain_exact h (t:ℝ))

/-- Choice indices are shared BEFORE any existential projection. -/
def familyDomain {W : Type*} (ws : List W) (b c : W → Band) (e : Expr) : DomainBounds ℝ :=
  exactInputDomain (fun _ w => w ∈ ws) (fun t w z => Values (b w) (c w) e t z)

def resultDomain {W : Type*} (ws : List W) (r : W → Result) : DomainBounds ℝ :=
  exactInputDomain (fun _ w => w ∈ ws) (fun t w z => guardHolds (r w).domain t ∧ z=0)

theorem family_classification_exact {W : Type*} (ws : List W) (b c : W → Band)
    (e : Expr) (r : W → Result) (h : ∀ w ∈ ws, evaluate? (b w) (c w) e = some (r w))
    (t : ℝ) :
    (familyDomain ws b c e).definite t = (resultDomain ws r).definite t ∧
    (familyDomain ws b c e).possible t = (resultDomain ws r).possible t := by
  have hd (w : W) (hw : w ∈ ws) : guardHolds (r w).domain t ↔ ∃ z, Values (b w) (c w) e t z :=
    evaluate_domain_exact (h w hw) t
  apply And.intro <;> apply propext
  · change ((∃ w, w ∈ ws) ∧ ∀ w, w ∈ ws → ∃ z, Values (b w) (c w) e t z) ↔ _
    simp only [resultDomain,exactInputDomain,exists_eq_right]
    exact and_congr_right (fun _ => forall_congr' (fun w => imp_congr_right (fun hw => (hd w hw).symm)))
  · change (∃ w z, w ∈ ws ∧ Values (b w) (c w) e t z) ↔ _
    simp only [resultDomain,exactInputDomain,exists_and_left,exists_eq_right,exists_eq,and_true]
    exact exists_congr (fun w => and_congr_right (fun hw => (hd w hw).symm))

theorem family_encloses {W : Type*} (ws : List W) (b c : W → Band)
    (e : Expr) (r : W → Result) (h : ∀ w ∈ ws, evaluate? (b w) (c w) e = some (r w))
    {w : W} (hw : w ∈ ws) {t z : ℝ} (hv : Values (b w) (c w) e t z) :
    (r w).values.Contains t z := evaluate_encloses (h w hw) hv
end GeneralizedIntervalArithmetic.GuardedPieceComposition
