import SourceRoundedAlgebra
import IntervalAlgebra

/-! Source audit control for §2.7.5: exact real interval subdistributivity
must not be silently transferred to staged, least outward rounding. -/
namespace GeneralizedIntervalArithmetic.RoundedIntervalControl
open FiniteFormat DirectedOperationAlgebra SourceRoundedAlgebra

/-- Each endpoint is the least outward bound in the specified finite format. -/
def Outward (D : Finset ℚ) (I J : QInterval) : Prop :=
  J.lo ∈ D ∧ J.hi ∈ D ∧
  DiscreteDemotion.down D (I.lo:ℝ) = ((J.lo:ℝ):EReal) ∧
  DiscreteDemotion.up D (I.hi:ℝ) = ((J.hi:ℝ):EReal)

def interval (a b : ℚ) (h : a≤b) : QInterval := ⟨a,b,h⟩

theorem gap202 {q : ℚ} (h : q∈values literal) : q≤200 ∨ 210≤q := by
  obtain ⟨a,e,ha,hb,he,hf,rfl⟩ := (mem_values literal q).1 h
  clear h
  norm_num [literal,bound,shift] at ha hb he hf
  by_contra hh
  push_neg at hh
  unfold value at hh
  norm_num [literal] at hh
  have hel : -11≤e := by omega
  have heu : e≤7 := by omega
  have haq : (-100:ℚ)<a := by exact_mod_cast ha
  have hbq : (a:ℚ)<100 := by exact_mod_cast hb
  interval_cases e <;> norm_num at hh <;> first | (norm_cast at hh; omega) | linarith [hh.1,hh.2]

theorem m200 : (200:ℚ)∈values literal := by
  convert literal_scaled 20 1 (by norm_num) using 1; norm_num
theorem m210 : (210:ℚ)∈values literal := by
  convert literal_scaled 21 1 (by norm_num) using 1; norm_num
theorem m220 : (220:ℚ)∈values literal := by
  convert literal_scaled 22 1 (by norm_num) using 1; norm_num

theorem round101 : Rounded (values literal) 101 100 110 :=
  gap_round (literal_constants (by simp)) (literal_constants (by simp))
    (by norm_num) (by norm_num) (fun _ h => literal_gap_small h)

theorem round202 : Rounded (values literal) 202 200 210 :=
  gap_round m200 m210 (by norm_num) (by norm_num) (fun _ h => gap202 h)

/-- Actual rational interval operations followed by certified least rounding
at every node. No arbitrary extra widening is used in the counterexample. -/
theorem staged :
    let D := values literal
    let I := interval 2 2 (by norm_num)
    let J := interval 100 100 (by norm_num)
    let K := interval 1 1 (by norm_num)
    let S := interval 100 110 (by norm_num)
    let L := interval 200 220 (by norm_num)
    let P := interval 200 200 (by norm_num)
    let Q := interval 2 2 (by norm_num)
    let R := interval 200 210 (by norm_num)
    Outward D (J.add K) S ∧ Outward D (I.mul S) L ∧
      Outward D (I.mul J) P ∧ Outward D (I.mul K) Q ∧
      Outward D (P.add Q) R ∧ L.Contains 220 ∧ ¬R.Contains 220 := by
  have h101 := round101
  have h202 := round202
  have h200 := exact_representable m200
  have h220 := exact_representable m220
  have h2 := exact_representable (literal_constants (q:=2) (by simp))
  norm_num [Rounded] at h101 h202 h200 h220 h2
  norm_num [Outward,interval,QInterval.add,QInterval.mul,QInterval.Contains]
  tauto

end GeneralizedIntervalArithmetic.RoundedIntervalControl
