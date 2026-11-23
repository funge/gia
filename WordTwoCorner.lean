import Binary64
import TwoCornerRefinement

namespace GeneralizedIntervalArithmetic.WordTwoCorner
open HardwareAddition
abbrev Word := Binary64.Word
abbrev Requests (F : Type) := (F × F) × (F × F)

structure Aperture where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving Repr

/-- Decode ALL endpoints, then check both orders and strict separation. -/
def validate (I J : Bounds Word) : Option Aperture := do
  let a ← Binary64.decode I.lo
  let b ← Binary64.decode I.hi
  let c ← Binary64.decode J.lo
  let d ← Binary64.decode J.hi
  if a ≤ b ∧ c ≤ d ∧ (0 < c ∨ d < 0) then some ⟨a,b,c,d⟩ else none

def Valid (I J : Bounds Word) (q : Aperture) : Prop :=
  Binary64.decode I.lo = some q.a ∧ Binary64.decode I.hi = some q.b ∧
  Binary64.decode J.lo = some q.c ∧ Binary64.decode J.hi = some q.d ∧
  q.a ≤ q.b ∧ q.c ≤ q.d ∧ (0 < q.c ∨ q.d < 0)

theorem validate_spec {I J : Bounds Word} {q : Aperture}
    (h : validate I J = some q) : Valid I J q := by
  unfold validate at h
  cases ha : Binary64.decode I.lo <;> simp only [ha,bind,pure,Option.bind] at h
  · contradiction
  next a =>
    cases hb : Binary64.decode I.hi <;> simp only [hb,bind,pure,Option.bind] at h
    · contradiction
    next b =>
      cases hc : Binary64.decode J.lo <;> simp only [hc,bind,pure,Option.bind] at h
      · contradiction
      next c =>
        cases hd : Binary64.decode J.hi <;> simp only [hd,bind,pure,Option.bind] at h
        · contradiction
        next d =>
          split_ifs at h with hv
          cases h
          exact ⟨ha,hb,hc,hd,hv⟩

/-- Pure rational sign tests select the ORIGINAL words; zeros are not normalized. -/
def pick {F : Type} (q : Aperture) (I J : Bounds F) : Requests F :=
  if 0 < q.c then
    if 0 ≤ q.a then ((I.lo,J.hi),(I.hi,J.lo)) else
    if q.b ≤ 0 then ((I.lo,J.lo),(I.hi,J.hi)) else ((I.lo,J.lo),(I.hi,J.lo))
  else
    if 0 ≤ q.a then ((I.hi,J.hi),(I.lo,J.lo)) else
    if q.b ≤ 0 then ((I.hi,J.lo),(I.lo,J.hi)) else ((I.hi,J.hi),(I.lo,J.hi))

def requests (I J : Bounds Word) : Option (Requests Word) := do
  let q ← validate I J
  return pick q I J

noncomputable def realCorners (q : Aperture) : TwoCornerDivision.Corners :=
  pick q ⟨q.a,q.b⟩ ⟨q.c,q.d⟩

def Decodes (w : Requests Word) (p : TwoCornerDivision.Corners) : Prop :=
  Binary64.real w.1.1 = some p.1.1 ∧ Binary64.real w.1.2 = some p.1.2 ∧
  Binary64.real w.2.1 = some p.2.1 ∧ Binary64.real w.2.2 = some p.2.2

theorem pick_decodes {I J : Bounds Word} {q : Aperture} (h : Valid I J q) :
    Decodes (pick q I J) (realCorners q) := by
  obtain ⟨ha,hb,hc,hd,_⟩ := h
  by_cases hpos : 0 < q.c <;> by_cases hlo : 0 ≤ q.a <;> by_cases hhi : q.b ≤ 0 <;>
    simp [Decodes,pick,realCorners,hpos,hlo,hhi,Binary64.real,ha,hb,hc,hd]

theorem pick_select {I J : Bounds Word} {q : Aperture} (h : Valid I J q) :
    TwoCornerDivision.select q.a q.b q.c q.d = some (realCorners q) := by
  obtain ⟨_,_,_,_,hab,hcd,hg⟩ := h
  have habR : (q.a:ℝ) ≤ q.b := by exact_mod_cast hab
  have hcdR : (q.c:ℝ) ≤ q.d := by exact_mod_cast hcd
  by_cases hp : 0 < q.c <;> by_cases ha : 0 ≤ q.a <;> by_cases hb : q.b ≤ 0
  all_goals
    have hpR : (0 < (q.c:ℝ)) ↔ 0 < q.c := by exact_mod_cast (Iff.rfl : (0:ℚ) < q.c ↔ 0 < q.c)
    have haR : (0 ≤ (q.a:ℝ)) ↔ 0 ≤ q.a := by exact_mod_cast (Iff.rfl : (0:ℚ) ≤ q.a ↔ 0 ≤ q.a)
    have hbR : ((q.b:ℝ) ≤ 0) ↔ q.b ≤ 0 := by exact_mod_cast (Iff.rfl : q.b ≤ (0:ℚ) ↔ q.b ≤ 0)
    have hn : ¬ 0 < q.c → (q.d:ℝ) < 0 := fun hn => by exact_mod_cast hg.resolve_left hn
    simp [TwoCornerDivision.select,TwoCornerDivision.positiveCorners,
      TwoCornerDivision.negativeCorners,realCorners,pick,habR,hcdR,hpR,haR,hbR,hp,ha,hb,
      show ¬ 0 < q.c → (q.d:ℝ) < 0 from hn]

theorem requests_spec {I J : Bounds Word} {p : Requests Word}
    (h : requests I J = some p) : ∃ q, Valid I J q ∧ p = pick q I J ∧
      TwoCornerDivision.select q.a q.b q.c q.d = some (realCorners q) ∧
      Decodes p (realCorners q) := by
  unfold requests at h
  cases hv : validate I J <;> simp only [hv,bind,pure,Option.bind] at h
  · contradiction
  next q =>
    cases h
    have hs := validate_spec hv
    exact ⟨q,hs,rfl,pick_select hs,pick_decodes hs⟩

/-- An instrumented pure executor. A trace entry is recorded exactly when a
paired call is dispatched. Invalid input reaches neither call; first failure
short-circuits the second. This is not a trace of native fenv/instructions. -/
def run (call : Word → Word → Option (Word × Word)) (I J : Bounds Word) :
    List (Word × Word) × Option (Bounds Word) :=
  match requests I J with
  | none => ([],none)
  | some p => match call p.1.1 p.1.2 with
    | none => ([p.1],none)
    | some lo => ([p.1,p.2],assemble (some lo) (call p.2.1 p.2.2))

theorem rejected_no_calls (call : Word → Word → Option (Word × Word))
    {I J : Bounds Word} (h : requests I J = none) : run call I J = ([],none) := by
  simp [run,h]

theorem invalid_no_calls (call : Word → Word → Option (Word × Word))
    {I J : Bounds Word} (h : ¬ ∃ q, Valid I J q) : run call I J = ([],none) := by
  apply rejected_no_calls
  cases hp : requests I J with
  | none => rfl
  | some p =>
    obtain ⟨q,hq,_⟩ := requests_spec hp
    exact (h ⟨q,hq⟩).elim

theorem result_eq (call : Word → Word → Option (Word × Word))
    {I J : Bounds Word} {p : Requests Word} (h : requests I J = some p) :
    (run call I J).2 = assemble (call p.1.1 p.1.2) (call p.2.1 p.2.2) := by
  simp only [run,h]
  cases hc : call p.1.1 p.1.2 <;> simp [assemble]

/-- Standalone soundness needs ONLY the two selected observed contracts, not
old four-corner success. Executable validation discharges all input/selection facts. -/
theorem run_sound {call : Word → Word → Option (Word × Word)} {I J O : Bounds Word}
    (hc : ∀ p, requests I J = some p →
      HardwareDivision.CallSound Binary64.real p.1.1 p.1.2 (call p.1.1 p.1.2) ∧
      HardwareDivision.CallSound Binary64.real p.2.1 p.2.2 (call p.2.1 p.2.2))
    (ho : (run call I J).2 = some O) {x y : ℝ}
    (hx : Contains Binary64.real I x) (hy : Contains Binary64.real J y) :
    Contains Binary64.real O (x/y) ∧ y ≠ 0 := by
  cases hp : requests I J with
  | none => simp [run,hp] at ho
  | some p =>
    obtain ⟨q,hv,_,hs,hd⟩ := requests_spec hp
    obtain ⟨ha,hb,hc',hd',_⟩ := hv
    have bounds {A : Bounds Word} {a b : ℚ} (ha : Binary64.decode A.lo = some a)
        (hb : Binary64.decode A.hi = some b) {z : ℝ} (hz : Contains Binary64.real A z) :
        (a:ℝ) ≤ z ∧ z ≤ b := by
      rcases hz with ⟨l,u,hl,hu,hz⟩
      have el : l = (a:ℝ) := by simpa [Binary64.real,ha] using hl.symm
      have eu : u = (b:ℝ) := by simpa [Binary64.real,hb] using hu.symm
      subst l; subst u; exact hz
    exact TwoCornerDivision.assemble_selected_encloses hs hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
      (hc p hp).1 (hc p hp).2 ((result_eq call hp).symm.trans ho)
      (bounds ha hb hx) (bounds hc' hd' hy)

/-- Separate, one-way comparison with the old assembly. The retained directions
must be matching decoded observations, with operand/outcome associations; this
is not a consequence of two independently sound executors. -/
theorem run_refines {call : Word → Word → Option (Word × Word)}
    {I J : Bounds Word} {p : Requests Word} (hp : requests I J = some p)
    {mn mx : Word → Word → Word}
    (hmin : HardwareMultiplication.SelectSound Binary64.real mn min)
    (hmax : HardwareMultiplication.SelectSound Binary64.real mx max)
    {ll lh hl hh lower upper : Option (Word × Word)} {old : Bounds Word}
    {v₁ v₂ v₃ v₄ : ℝ}
    (h₁ : HardwareMultiplication.ResultSound Binary64.real ll v₁)
    (h₂ : HardwareMultiplication.ResultSound Binary64.real lh v₂)
    (h₃ : HardwareMultiplication.ResultSound Binary64.real hl v₃)
    (h₄ : HardwareMultiplication.ResultSound Binary64.real hh v₄)
    (hL : (p.1,lower) ∈ TwoCornerRefinement.observations I J ll lh hl hh)
    (hU : (p.2,upper) ∈ TwoCornerRefinement.observations I J ll lh hl hh)
    (hD : TwoCornerRefinement.downValue Binary64.real (call p.1.1 p.1.2) =
      TwoCornerRefinement.downValue Binary64.real lower)
    (hUp : TwoCornerRefinement.upValue Binary64.real (call p.2.1 p.2.2) =
      TwoCornerRefinement.upValue Binary64.real upper)
    (hold : HardwareMultiplication.assembleFour mn mx ll lh hl hh = some old) :
    ∃ new, (run call I J).2 = some new ∧ TwoCornerRefinement.Refines Binary64.real new old := by
  obtain ⟨new,hn,hr⟩ := TwoCornerRefinement.directional_observations_refine hmin hmax
    h₁ h₂ h₃ h₄ (TwoCornerRefinement.observed_mem hL) (TwoCornerRefinement.observed_mem hU)
    hD hUp hold
  exact ⟨new,(result_eq call hp).trans hn,hr⟩

end GeneralizedIntervalArithmetic.WordTwoCorner
