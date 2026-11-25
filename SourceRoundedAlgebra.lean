import DirectedOperationAlgebra
import FormatNormalization
import ExceptionalComparisons
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace GeneralizedIntervalArithmetic.SourceRoundedAlgebra
open FiniteFormat DirectedOperationAlgebra

@[irreducible] def literal : Format := ⟨10,3,-9,9,by decide,by decide,by decide⟩
/-- Reindexing device for the three-digit repair, not a change to literal. -/
@[irreducible] def repairedIndex : Format := ⟨10,4,-8,10,by decide,by decide,by decide⟩

theorem repaired_correspondence (q : ℚ) : q ∈ values repairedIndex ↔ FormatDigits.Repaired literal q := by
  rw [mem_values,FormatDigits.repaired_coefficients]
  norm_num only [repairedIndex,literal,bound,shift,value, Nat.reduceSub, Int.reducePow, Nat.cast_ofNat]
  constructor <;> rintro ⟨a,e,ha,hb,he,hf,hq⟩ <;> exact ⟨a,e,ha,hb,by omega,by omega,hq⟩

theorem literal_gap {q : ℚ} (h : q ∈ values literal) : q ≤ 1000 ∨ 1100 ≤ q := by
  obtain ⟨a,e,ha,hb,he,hf,rfl⟩ := (mem_values literal q).1 h
  clear h
  norm_num [literal,repairedIndex,bound,shift] at ha hb he hf
  by_contra hh
  push_neg at hh
  unfold value at hh
  norm_num [literal] at hh
  have hel : -11 ≤ e := by omega
  have heu : e ≤ 7 := by omega
  have haq : (-100:ℚ) < a := by exact_mod_cast ha
  have hbq : (a:ℚ) < 100 := by exact_mod_cast hb
  interval_cases e <;> norm_num at hh <;> first | (norm_cast at hh; omega) | linarith [hh.1,hh.2]

theorem literal_gap_small {q : ℚ} (h : q ∈ values literal) : q ≤ 100 ∨ 110 ≤ q := by
  obtain ⟨a,e,ha,hb,he,hf,rfl⟩ := (mem_values literal q).1 h
  clear h
  norm_num [literal,repairedIndex,bound,shift] at ha hb he hf
  by_contra hh
  push_neg at hh
  unfold value at hh
  norm_num [literal] at hh
  have hel : -11 ≤ e := by omega
  have heu : e ≤ 7 := by omega
  have haq : (-100:ℚ) < a := by exact_mod_cast ha
  have hbq : (a:ℚ) < 100 := by exact_mod_cast hb
  interval_cases e <;> norm_num at hh <;> first | (norm_cast at hh; omega) | linarith [hh.1,hh.2]

theorem literal_gap_high {q : ℚ} (h : q ∈ values literal) : q ≤ 99000 ∨ 100000 ≤ q := by
  obtain ⟨a,e,ha,hb,he,hf,rfl⟩ := (mem_values literal q).1 h
  clear h
  norm_num [literal,repairedIndex,bound,shift] at ha hb he hf
  by_contra hh
  push_neg at hh
  unfold value at hh
  norm_num [literal] at hh
  have hel : -11 ≤ e := by omega
  have heu : e ≤ 7 := by omega
  have haq : (-100:ℚ) < a := by exact_mod_cast ha
  have hbq : (a:ℚ) < 100 := by exact_mod_cast hb
  interval_cases e <;> norm_num at hh <;> first | (norm_cast at hh; omega) | linarith [hh.1,hh.2]

theorem repaired_gap {q : ℚ} (h : q ∈ values repairedIndex) : q ≤ 1000 ∨ 1010 ≤ q := by
  obtain ⟨a,e,ha,hb,he,hf,rfl⟩ := (mem_values repairedIndex q).1 h
  clear h
  norm_num [literal,repairedIndex,bound,shift] at ha hb he hf
  by_contra hh
  push_neg at hh
  unfold value at hh
  norm_num [repairedIndex] at hh
  have hel : -11 ≤ e := by omega
  have heu : e ≤ 7 := by omega
  have haq : (-1000:ℚ) < a := by exact_mod_cast ha
  have hbq : (a:ℚ) < 1000 := by exact_mod_cast hb
  interval_cases e <;> norm_num at hh <;> first | (norm_cast at hh; omega) | linarith [hh.1,hh.2]

theorem repaired_gap_high {q : ℚ} (h : q ∈ values repairedIndex) : q ≤ 99900 ∨ 100000 ≤ q := by
  obtain ⟨a,e,ha,hb,he,hf,rfl⟩ := (mem_values repairedIndex q).1 h
  clear h
  norm_num [literal,repairedIndex,bound,shift] at ha hb he hf
  by_contra hh
  push_neg at hh
  unfold value at hh
  norm_num [repairedIndex] at hh
  have hel : -11 ≤ e := by omega
  have heu : e ≤ 7 := by omega
  have haq : (-1000:ℚ) < a := by exact_mod_cast ha
  have hbq : (a:ℚ) < 1000 := by exact_mod_cast hb
  interval_cases e <;> norm_num at hh <;> first | (norm_cast at hh; omega) | linarith [hh.1,hh.2]

theorem member (F : Format) (a e : ℤ) (ha : -(bound F)<a) (hb : a<bound F)
    (hl : F.minExponent≤e+shift F) (hu : e+shift F≤F.maxExponent) :
    value F a e ∈ values F := (mem_values F _).2 ⟨a,e,ha,hb,hl,hu,rfl⟩

theorem neg_member (F : Format) {q : ℚ} (hq : q ∈ values F) : -q ∈ values F := by
  obtain ⟨a,e,ha,hb,hl,hu,rfl⟩ := (mem_values F q).1 hq
  apply (mem_values F _).2
  exact ⟨-a,e,by omega,by omega,hl,hu,by simp [value]⟩

theorem reflect_gap (F : Format) {l u : ℚ}
    (h : ∀ q ∈ values F, q≤l ∨ u≤q) {q : ℚ} (hq : q∈values F) : q≤-u ∨ -l≤q := by
  rcases h (-q) (neg_member F hq) with hl | hu
  · right; linarith
  · left; linarith

theorem gap_round {D : Finset ℚ} {l u x : ℚ} (hl : l∈D) (hu : u∈D)
    (hx : l<x) (hy : x<u) (hg : ∀q∈D,q≤l ∨ u≤q) : Rounded D x l u := by
  apply (rounded_iff_extremal _ _ _ _).2
  refine ⟨hl,hu,by exact_mod_cast hx.le,by exact_mod_cast hy.le,?_,?_⟩
  · intro q hq hqx
    have hqx' : q≤x := by exact_mod_cast hqx
    rcases hg q hq with h | h
    · exact h
    · linarith
  · intro q hq hxq
    have hxq' : x≤q := by exact_mod_cast hxq
    rcases hg q hq with h | h
    · linarith
    · exact h

/-- Nearest is a specification; ties are deliberately not selected. -/
def Nearest (D : Finset ℚ) (x q : ℚ) : Prop := q∈D ∧ ∀r∈D, |x-q|≤|x-r|
def StrictNearest (D : Finset ℚ) (x q : ℚ) : Prop := q∈D ∧ ∀r∈D,r≠q → |x-q| < |x-r|

theorem strict_forces {D : Finset ℚ} {x q r : ℚ}
    (h : StrictNearest D x q) (k : Nearest D x r) : r=q := by
  by_contra hn
  exact (not_lt_of_ge (k.2 q h.1)) (h.2 r k.1 hn)

theorem strict_below {D : Finset ℚ} {l u x : ℚ} (hl : l∈D)
    (hx : l≤x) (_hy : x≤u) (hc : x-l<u-x)
    (hg : ∀q∈D,q≤l ∨ u≤q) : StrictNearest D x l := by
  refine ⟨hl,?_⟩
  intro q hq hn
  rw [abs_of_nonneg (sub_nonneg.mpr hx)]
  rcases hg q hq with h | h
  · rw [abs_of_nonneg (by linarith)]
    have := lt_of_le_of_ne h hn
    linarith
  · rw [abs_of_nonpos (by linarith)]
    linarith

theorem strict_above {D : Finset ℚ} {l u x : ℚ} (hu : u∈D)
    (_hx : l≤x) (hy : x≤u) (hc : u-x<x-l)
    (hg : ∀q∈D,q≤l ∨ u≤q) : StrictNearest D x u := by
  refine ⟨hu,?_⟩
  intro q hq hn
  rw [abs_of_nonpos (sub_nonpos.mpr hy)]
  rcases hg q hq with h | h
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonpos (by linarith)]
    have : u<q := lt_of_le_of_ne h (Ne.symm hn)
    linarith


theorem literal_scaled (a e : ℤ) (h : -100<a ∧ a<100 ∧ -11≤e ∧ e≤7) :
    (a:ℚ)*10^e ∈ values literal := by
  apply (mem_values literal _).2
  refine ⟨a,e,?_,?_,?_,?_,?_⟩ <;> norm_num [literal,bound,shift,value] at * <;> omega

theorem repaired_scaled (a e : ℤ) (h : -1000<a ∧ a<1000 ∧ -11≤e ∧ e≤7) :
    (a:ℚ)*10^e ∈ values repairedIndex := by
  apply (mem_values repairedIndex _).2
  refine ⟨a,e,?_,?_,?_,?_,?_⟩ <;> norm_num [repairedIndex,bound,shift,value] at * <;> omega

theorem literal_constants {q : ℚ} (h : q ∈ ([0,1,2,3,34,17,51,50,55,100,110,1000,1100,100000,99000,-100,-50,10,1/2] : List ℚ)) : q ∈ values literal := by
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · convert literal_scaled (0) (0) (by norm_num) using 1; norm_num
  · convert literal_scaled (1) (0) (by norm_num) using 1; norm_num
  · convert literal_scaled (2) (0) (by norm_num) using 1; norm_num
  · convert literal_scaled (3) (0) (by norm_num) using 1; norm_num
  · convert literal_scaled (34) (0) (by norm_num) using 1; norm_num
  · convert literal_scaled (17) (0) (by norm_num) using 1; norm_num
  · convert literal_scaled (51) (0) (by norm_num) using 1; norm_num
  · convert literal_scaled (50) (0) (by norm_num) using 1; norm_num
  · convert literal_scaled (55) (0) (by norm_num) using 1; norm_num
  · convert literal_scaled (10) (1) (by norm_num) using 1; norm_num
  · convert literal_scaled (11) (1) (by norm_num) using 1; norm_num
  · convert literal_scaled (10) (2) (by norm_num) using 1; norm_num
  · convert literal_scaled (11) (2) (by norm_num) using 1; norm_num
  · convert literal_scaled (10) (4) (by norm_num) using 1; norm_num
  · convert literal_scaled (99) (3) (by norm_num) using 1; norm_num
  · convert literal_scaled (-10) (1) (by norm_num) using 1; norm_num
  · convert literal_scaled (-50) (0) (by norm_num) using 1; norm_num
  · convert literal_scaled (10) (0) (by norm_num) using 1; norm_num
  · convert literal_scaled (5) (-1) (by norm_num) using 1; norm_num

theorem decimal_literal : Rounded (values literal) 1001 1000 1100 :=
  gap_round (literal_constants (by simp)) (literal_constants (by simp))
    (by norm_num) (by norm_num) (fun _ h => literal_gap h)
theorem decimal_repaired : Rounded (values repairedIndex) 1001 1000 1010 := by
  have hl : (1000:ℚ)∈values repairedIndex := by
    convert repaired_scaled 100 1 (by norm_num) using 1; norm_num
  have hu : (1010:ℚ)∈values repairedIndex := by
    convert repaired_scaled 101 1 (by norm_num) using 1; norm_num
  exact gap_round hl hu (by norm_num) (by norm_num) (fun _ h => repaired_gap h)

theorem decimal_nearest_literal : StrictNearest (values literal) 1001 1000 :=
  strict_below (literal_constants (by simp)) (by norm_num) (by norm_num)
    (by norm_num) (fun _ h => literal_gap h)
theorem decimal_nearest_repaired : StrictNearest (values repairedIndex) 1001 1000 := by
  have hl : (1000:ℚ)∈values repairedIndex := by
    convert repaired_scaled 100 1 (by norm_num) using 1; norm_num
  exact strict_below hl (by norm_num) (by norm_num) (by norm_num) (fun _ h => repaired_gap h)

theorem cancellation_literal : Rounded (values literal) (-99999) (-100000) (-99000) := by
  have h := gap_round (neg_member literal (literal_constants (q:=100000) (by simp)))
    (neg_member literal (literal_constants (q:=99000) (by simp)))
    (x:=(-99999)) (by norm_num) (by norm_num)
    (fun q hq => reflect_gap literal (fun _ h => literal_gap_high h) hq)
  simpa using h

theorem cancellation_repaired : Rounded (values repairedIndex) (-99999) (-100000) (-99900) := by
  have hl : (100000:ℚ)∈values repairedIndex := by
    convert repaired_scaled 100 3 (by norm_num) using 1; norm_num
  have hu : (99900:ℚ)∈values repairedIndex := by
    convert repaired_scaled 999 2 (by norm_num) using 1; norm_num
  simpa using gap_round (neg_member _ hl) (neg_member _ hu) (x:=(-99999)) (by norm_num) (by norm_num)
    (fun _ h => reflect_gap repairedIndex (fun _ h => repaired_gap_high h) h)

inductive Mode | down | up | nearest deriving DecidableEq

def Rounds (D : Finset ℚ) : Mode → ℚ → ℚ → Prop
  | .down,x,q => ∃u,Rounded D x q u
  | .up,x,q => ∃l,Rounded D x l q
  | .nearest,x,q => Nearest D x q

theorem exact_forces {D : Finset ℚ} {x q : ℚ} (hx : x∈D) (m : Mode)
    (h : Rounds D m x q) : q=x := by
  cases m with
  | down => obtain ⟨u,hu⟩ := h; exact (rounded_unique hu (exact_representable hx)).1
  | up => obtain ⟨l,hl⟩ := h; exact (rounded_unique hl (exact_representable hx)).2
  | nearest =>
    have hh := h.2 x hx
    simp only [sub_self,abs_zero] at hh
    have he := abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    linarith

theorem small_round : Rounded (values literal) 102 100 110 :=
  gap_round (literal_constants (by simp)) (literal_constants (by simp))
    (by norm_num) (by norm_num) (fun _ h => literal_gap_small h)
theorem small_nearest : StrictNearest (values literal) 102 100 :=
  strict_below (literal_constants (by simp)) (by norm_num) (by norm_num)
    (by norm_num) (fun _ h => literal_gap_small h)

def smallResult : Mode → ℚ | .up => 110 | _ => 100

theorem small_forces (m : Mode) {q : ℚ} (h : Rounds (values literal) m 102 q) :
    q=smallResult m := by
  cases m with
  | down => obtain ⟨u,hu⟩ := h; exact (rounded_unique hu small_round).1
  | up => obtain ⟨l,hl⟩ := h; exact (rounded_unique hl small_round).2
  | nearest => exact strict_forces small_nearest h

/-- Only local required observations are assumed; no totality or tie policy. -/
theorem multiplication_nonassoc (r : Mode → ℚ → ℚ) (m : Mode)
    (h102 : Rounds (values literal) m 102 (r m 102))
    (h50 : Rounds (values literal) m 50 (r m 50))
    (h55 : Rounds (values literal) m 55 (r m 55))
    (h17 : Rounds (values literal) m 17 (r m 17))
    (h51 : Rounds (values literal) m 51 (r m 51)) :
    r m (r m (3*34)*(1/2)) ≠ r m (3*r m (34*(1/2))) := by
  have e102 := small_forces m h102
  have e50 := exact_forces (literal_constants (q:=50) (by simp)) m h50
  have e55 := exact_forces (literal_constants (q:=55) (by simp)) m h55
  have e17 := exact_forces (literal_constants (q:=17) (by simp)) m h17
  have e51 := exact_forces (literal_constants (q:=51) (by simp)) m h51
  norm_num only at *
  rw [e102,e17]
  cases m <;> norm_num [smallResult] at * <;> simp_all

/-- One witness refutes every combination of the five rounding-mode sites.
The local exact-result hypotheses expose all finite availability requirements. -/
theorem mixed_distributivity (r : Mode → ℚ → ℚ)
    (m₁ m₂ m₃ m₄ m₅ : Mode)
    (h102 : Rounds (values literal) m₃ 102 (r m₃ 102))
    (hex : ∀m,∀q∈([0,1,2,10,-100]:List ℚ),Rounds (values literal) m q (r m q)) :
    r m₂ (2*r m₁ (51+(-50))) ≠
      r m₅ (r m₃ (2*51) + r m₄ (2*(-50))) := by
  have e1 := exact_forces (literal_constants (q:=1) (by simp)) m₁ (hex _ _ (by simp))
  have e2 := exact_forces (literal_constants (q:=2) (by simp)) m₂ (hex _ _ (by simp))
  have en := exact_forces (literal_constants (q:=(-100)) (by simp)) m₄ (hex _ _ (by simp))
  have e0 := exact_forces (literal_constants (q:=0) (by simp)) m₅ (hex _ _ (by simp))
  have e10 := exact_forces (literal_constants (q:=10) (by simp)) m₅ (hex _ _ (by simp))
  have e102 := small_forces m₃ h102
  norm_num only at *
  rw [e1,en,e102]
  cases m₃ <;> norm_num [smallResult] at * <;> simp_all


theorem literal_up_not_printed : ¬ ∃ l, Rounded (values literal) 1001 l 1010 := by
  rintro ⟨l,h⟩
  have hh := (rounded_unique h decimal_literal).2
  norm_num at hh

theorem nearest_inner : StrictNearest (values literal) (-99999) (-100000) :=
  strict_below (neg_member literal (literal_constants (q:=100000) (by simp)))
    (by norm_num) (by norm_num) (by norm_num)
    (fun _ h => reflect_gap literal (fun _ h => literal_gap_high h) h)

def innerResult : Mode → ℚ | .up => -99000 | _ => -100000

theorem inner_forces (m : Mode) {q : ℚ} (h : Rounds (values literal) m (-99999) q) :
    q=innerResult m := by
  have hc : Rounded (values literal) ((-99999:ℚ):ℝ) (-100000) (-99000) := by simpa using cancellation_literal
  cases m with
  | down => obtain ⟨u,hu⟩ := h; exact (rounded_unique hu hc).1
  | up => obtain ⟨l,hl⟩ := h; exact (rounded_unique hl hc).2
  | nearest => exact strict_forces nearest_inner h

def rightResult : Mode → ℚ | .up => 1000 | _ => 0

/-- The printed nearest and upward rows reproduce in the literal coefficient
format. The downward row gives zero, not the printed 10000. -/
theorem printed_reassociation (r : Mode → ℚ → ℚ) (m : Mode)
    (hi : Rounds (values literal) m (-99999) (r m (-99999)))
    (he : ∀q∈([0,1,1000]:List ℚ),Rounds (values literal) m q (r m q)) :
    r m (r m (100000 + (-100000)) + 1) = 1 ∧
    r m (100000 + r m ((-100000)+1)) = rightResult m := by
  have e0 := exact_forces (literal_constants (q:=0) (by simp)) m (he _ (by simp))
  have e1 := exact_forces (literal_constants (q:=1) (by simp)) m (he _ (by simp))
  have e1000 := exact_forces (literal_constants (q:=1000) (by simp)) m (he _ (by simp))
  have ei := inner_forces m hi
  norm_num only at *
  rw [e0,ei]
  cases m <;> norm_num [innerResult,rightResult] at * <;> simp_all

/-- A commutative extension of the existing ideal-addition observations.
Only the reversed finite/positive-infinity row is added; finite arithmetic
here remains ideal and is not a rounded floating-point computation. -/
noncomputable def sourceAddObservation : ExceptionalComparisons.Value →
    ExceptionalComparisons.Value → Option ExceptionalComparisons.Value
  | .posInf, .finite _ => some .posInf
  | a,b => ExceptionalComparisons.addObservation a b

theorem reversed_positive_infinity (x : ℝ) :
    sourceAddObservation .posInf (.finite x) = some .posInf := rfl

theorem observation_extends {a b c : ExceptionalComparisons.Value}
    (h : ExceptionalComparisons.addObservation a b = some c) :
    sourceAddObservation a b = some c := by
  cases a <;> cases b <;> simp_all [sourceAddObservation,ExceptionalComparisons.addObservation]

theorem observation_comm (a b : ExceptionalComparisons.Value) :
    sourceAddObservation a b = sourceAddObservation b a := by
  cases a <;> cases b <;> simp [sourceAddObservation,ExceptionalComparisons.addObservation,_root_.add_comm]

theorem observation_finite (x y z : ℝ) :
    sourceAddObservation (.finite x) (.finite y) = some (.finite z) ↔
      PartialRealArithmetic.addRel x y z := ExceptionalComparisons.add_finite_agreement x y z

theorem exceptional_rows_still_missing :
    sourceAddObservation .negInf .posInf = none ∧
    sourceAddObservation .undefined .posInf = none ∧
    sourceAddObservation .posInf .undefined = none := ⟨rfl,rfl,rfl⟩


theorem strict_is_nearest {D : Finset ℚ} {x q : ℚ} (h : StrictNearest D x q) : Nearest D x q := by
  refine ⟨h.1,?_⟩
  intro r hr
  by_cases he : r=q
  · simp [he]
  · exact (h.2 r hr he).le

theorem rounds_exact {D : Finset ℚ} {x : ℚ} (hx : x∈D) (m : Mode) : Rounds D m x x := by
  cases m with
  | down => exact ⟨x,exact_representable hx⟩
  | up => exact ⟨x,exact_representable hx⟩
  | nearest => exact ⟨hx,by intro r _; simp⟩

theorem small_accepted (m : Mode) : Rounds (values literal) m 102 (smallResult m) := by
  cases m with
  | down => exact ⟨110,small_round⟩
  | up => exact ⟨100,small_round⟩
  | nearest => exact strict_is_nearest small_nearest

theorem inner_accepted (m : Mode) : Rounds (values literal) m (-99999) (innerResult m) := by
  have hc : Rounded (values literal) ((-99999:ℚ):ℝ) (-100000) (-99000) := by simpa using cancellation_literal
  cases m with
  | down => exact ⟨-99000,hc⟩
  | up => exact ⟨-100000,hc⟩
  | nearest => exact strict_is_nearest nearest_inner

end GeneralizedIntervalArithmetic.SourceRoundedAlgebra
