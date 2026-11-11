import HardwareCover
import HardwareCosine
import PiBounds

namespace GeneralizedIntervalArithmetic.HardwareQuadrants
open HardwareAddition HardwareSine

noncomputable def markValue : Mark → ℝ
  | .neg4 => -4 | .neg375 => -15/4 | .neg225 => -9/4 | .neg075 => -3/4
  | .pos075 => 3/4 | .pos225 => 9/4 | .pos375 => 15/4 | .pos4 => 4
  | .neg15 => -3/2 | .neg1 => -1 | .neg05 => -1/2 | .zero => 0
  | .pos05 => 1/2 | .pos1 => 1 | .pos15 => 3/2

noncomputable def modeValue : Mode → ℝ → ℝ
  | .sin => Real.sin | .cos => Real.cos
  | .negSin => fun x => -Real.sin x | .negCos => fun x => -Real.cos x

def Phase (mode : Mode) (a : ℝ) : Prop :=
  ∀ x, modeValue mode (x - a*Real.pi) = Real.sin x

theorem evaluate_encloses {F : Type} {decode : F → Option ℝ}
    {mul sub : Bounds F → Bounds F → Option (Bounds F)}
    (hm : OpSound decode mul (· * ·)) (hs : OpSound decode sub (· - ·))
    {sin cos : Bounds F → Option (Bounds F)} (hsin : RangeSound decode sin)
    (hcos : ∀ I O x, cos I = some O → Contains decode I x → Contains decode O (Real.cos x))
    {zero : F} (hz : decode zero = some 0) {P : Bounds F} (hp : Contains decode P Real.pi)
    {c : Cell F} {a : ℝ} (hc : decode c.coefficient = some a) (hid : Phase c.mode a)
    {I O : Bounds F} (hr : evaluate (m := Id) mul sub sin cos zero P c I = some O)
    {x : ℝ} (hx : Contains decode I x) : Contains decode O (Real.sin x) := by
  have hcoef : Contains decode (⟨c.coefficient,c.coefficient⟩ : Bounds F) a :=
    ⟨a,a,hc,hc,le_rfl,le_rfl⟩
  have hz' : Contains decode (⟨zero,zero⟩ : Bounds F) 0 := ⟨0,0,hz,hz,le_rfl,le_rfl⟩
  unfold evaluate at hr
  simp only [bind,pure] at hr
  split at hr <;> try contradiction
  next shift he =>
    have hshift := hm _ _ _ _ _ he hcoef hp
    split at hr <;> try contradiction
    next residual er =>
      have hres := hs _ _ _ _ _ er hx hshift
      have hout : Contains decode O (modeValue c.mode (x-a*Real.pi)) := by
        cases heq : c.mode with
        | sin => simp only [heq] at hr; exact hsin _ _ _ hr hres
        | cos => simp only [heq] at hr; exact hcos _ _ _ hr hres
        | negSin =>
          simp only [heq] at hr
          split at hr <;> try contradiction
          next R hR =>
            have h := hs _ _ _ _ _ hr hz' (hsin _ _ _ hR hres)
            simpa [modeValue,heq] using h
        | negCos =>
          simp only [heq] at hr
          split at hr <;> try contradiction
          next R hR =>
            have h := hs _ _ _ _ _ hr hz' (hcos _ _ _ hR hres)
            simpa [modeValue,heq] using h
      simpa only [hid x] using hout

theorem table_phases {F : Type} {decode : F → Option ℝ} {v : Mark → F}
    (hv : ∀ m, decode (v m) = some (markValue m)) :
    ∀ c ∈ table v, ∃ a, decode c.coefficient = some a ∧ Phase c.mode a := by
  intro c hc
  simp only [table,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨_,hv _,?_⟩; intro x; simp only [modeValue,markValue]
  · rw [show x - - (3:ℝ)/2*Real.pi = (x + Real.pi/2) + Real.pi by ring]
    simp [Real.cos_add_pi_div_two,Real.cos_sub_pi_div_two]
  · rw [show x - -(1:ℝ)*Real.pi = x + Real.pi by ring]
    simp [Real.cos_add_pi_div_two,Real.cos_sub_pi_div_two]
  · rw [show x - -(1:ℝ)/2*Real.pi = x + Real.pi/2 by ring]
    simp [Real.cos_add_pi_div_two,Real.cos_sub_pi_div_two]
  · simp [Real.cos_add_pi_div_two,Real.cos_sub_pi_div_two]
  · rw [show x - (1:ℝ)/2*Real.pi = x - Real.pi/2 by ring]
    simp [Real.cos_add_pi_div_two,Real.cos_sub_pi_div_two]
  · simp [Real.cos_add_pi_div_two,Real.cos_sub_pi_div_two]
  · rw [show x - (3:ℝ)/2*Real.pi = (x - Real.pi/2) - Real.pi by ring]
    simp [Real.cos_add_pi_div_two,Real.cos_sub_pi_div_two]

theorem table_valid {F : Type} {decode : F → Option ℝ} {v : Mark → F}
    (hv : ∀ m, decode (v m) = some (markValue m)) :
    ∀ c ∈ table v, Valid decode c.domain := by
  intro c hc
  simp only [table,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_,_,hv _,hv _⟩

/-- All shared cell boundaries are included; the cover has no holes. -/
theorem table_cover {F : Type} {decode : F → Option ℝ} {v : Mark → F}
    (hv : ∀ m, decode (v m) = some (markValue m))
    {x : ℝ} (hx : -4 ≤ x ∧ x ≤ 4) : ∃ c ∈ table v, Contains decode c.domain x := by
  by_cases h0 : x ≤ (-15/4 : ℝ)
  · refine ⟨⟨⟨v .neg4,v .neg375⟩,v .neg15,.cos⟩, by simp [table], _,_,hv _,hv _,?_,?_⟩ <;>
    norm_num [markValue] <;> linarith
  by_cases h1 : x ≤ (-9/4 : ℝ)
  · refine ⟨⟨⟨v .neg375,v .neg225⟩,v .neg1,.negSin⟩, by simp [table], _,_,hv _,hv _,?_,?_⟩ <;>
    norm_num [markValue] <;> linarith
  by_cases h2 : x ≤ (-3/4 : ℝ)
  · refine ⟨⟨⟨v .neg225,v .neg075⟩,v .neg05,.negCos⟩, by simp [table], _,_,hv _,hv _,?_,?_⟩ <;>
    norm_num [markValue] <;> linarith
  by_cases h3 : x ≤ (3/4 : ℝ)
  · refine ⟨⟨⟨v .neg075,v .pos075⟩,v .zero,.sin⟩, by simp [table], _,_,hv _,hv _,?_,?_⟩ <;>
    norm_num [markValue] <;> linarith
  by_cases h4 : x ≤ (9/4 : ℝ)
  · refine ⟨⟨⟨v .pos075,v .pos225⟩,v .pos05,.cos⟩, by simp [table], _,_,hv _,hv _,?_,?_⟩ <;>
    norm_num [markValue] <;> linarith
  by_cases h5 : x ≤ (15/4 : ℝ)
  · refine ⟨⟨⟨v .pos225,v .pos375⟩,v .pos1,.negSin⟩, by simp [table], _,_,hv _,hv _,?_,?_⟩ <;>
    norm_num [markValue] <;> linarith
  refine ⟨⟨⟨v .pos375,v .pos4⟩,v .pos15,.negCos⟩, by simp [table], _,_,hv _,hv _,?_,?_⟩ <;>
  norm_num [markValue] <;> linarith

/-- Ideal reduction with any pi inside its certified dyadic bracket fits the
local kernels. This is not a totality/rounding-width theorem for loose adapters. -/
theorem ideal_cells_fit {c : Cell ℝ} (hc : c ∈ table markValue) {x p : ℝ}
    (hx : c.domain.lo ≤ x ∧ x ≤ c.domain.hi)
    (hp : HardwarePi.lower ≤ p ∧ p ≤ HardwarePi.upper) :
    -1 ≤ x - c.coefficient*p ∧ x - c.coefficient*p ≤ 1 := by
  simp only [table,List.mem_cons,List.not_mem_nil,or_false] at hc
  norm_num [HardwarePi.lower,HardwarePi.upper] at hp
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [markValue] at hx ⊢; constructor <;> linarith

theorem guard_four {F : Type} {decode : F → Option ℝ} {lt : F → F → Bool}
    (hc : HardwareDivision.CompareSound decode lt) {v : Mark → F}
    (hv : ∀ m, decode (v m) = some (markValue m)) {I : Bounds F}
    (hg : unitGuard lt (v .neg4) (v .pos4) I = true)
    {x : ℝ} (hx : Contains decode I x) : -4 ≤ x ∧ x ≤ 4 := by
  rcases hx with ⟨a,b,ha,hb,hl,hu⟩
  simp only [unitGuard,Bool.and_eq_true,Bool.not_eq_true'] at hg
  have hna : ¬ a < -4 := by
    intro h
    have hh := (hc _ _ _ _ ha (hv .neg4)).mpr h
    simp [hg.1.1] at hh
  have hnb : ¬ 4 < b := by
    intro h
    have hh := (hc _ _ _ _ (hv .pos4) hb).mpr h
    simp [hg.1.2] at hh
  exact ⟨(le_of_not_gt hna).trans hl,hu.trans (le_of_not_gt hnb)⟩

/-- Full pipeline: every real input in the accepted interval is covered. The
contracts prove successful results sound; they do not promise backend success. -/
theorem quadrants_enclose {F : Type} {decode : F → Option ℝ} {lt : F → F → Bool}
    {mn mx : F → F → F} (hc : HardwareDivision.CompareSound decode lt)
    (hmin : HardwareMultiplication.SelectSound decode mn min)
    (hmax : HardwareMultiplication.SelectSound decode mx max)
    {mul sub : Bounds F → Bounds F → Option (Bounds F)}
    (hm : OpSound decode mul (· * ·)) (hs : OpSound decode sub (· - ·))
    {sin cos : Bounds F → Option (Bounds F)} (hsin : RangeSound decode sin)
    (hcos : ∀ I O x, cos I = some O → Contains decode I x → Contains decode O (Real.cos x))
    {v : Mark → F} (hv : ∀ m, decode (v m) = some (markValue m))
    {P : Bounds F} (hp : Contains decode P Real.pi) {I O : Bounds F}
    (hr : run (m := Id) (unitGuard lt (v .neg4) (v .pos4)) lt mn mx
      (evaluate (m := Id) mul sub sin cos (v .zero) P) (table v) I = some O)
    {x : ℝ} (hx : Contains decode I x) : Contains decode O (Real.sin x) := by
  apply run_encloses hc hmin hmax (table_valid hv) ?_ ?_ hr hx
  · intro c hc' J O x hr hx
    obtain ⟨a,ha,hi⟩ := table_phases hv c hc'
    exact evaluate_encloses hm hs hsin hcos (hv .zero) hp ha hi hr hx
  · intro hg x hx
    exact table_cover hv (guard_four hc hv hg hx)

end GeneralizedIntervalArithmetic.HardwareQuadrants
