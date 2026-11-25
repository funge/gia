import FiniteQuery
import AuditPolicy
namespace GeneralizedIntervalArithmetic.FiniteQueryChecks
open FiniteQuery

/-- Out-of-order, repeated, reply-dependent requests, followed by a halt. -/
def reader : Machine ℕ
  | 0 => .inr (4, fun I => if I.lo < 1/10 then 1 else 3)
  | 1 => .inr (0, fun _ => 2)
  | 2 => .inr (4, fun _ => 3)
  | _ => .inl 1

theorem observed_trace : queries reader (straddle (1/10)) 4 0 = [4,0,4] ∧
    queriedBound reader (straddle (1/10)) 4 0 = 4 := by
  norm_num [queries,queriedBound,reader,straddle,radius]

theorem actual_collision : run reader (straddle (1/10)) 4 0 = some 1 ∧
    run reader (splice (1/10) 4) 4 0 = some 1 := by
  norm_num [run,reader,splice,straddle,radius]

theorem wrong_on_second : DigitExtraction.digits 10 (below (1/10) 4) 0 = 0 :=
  (decimal_below 4).2

theorem delayed_difference : splice (1/10) 4 4 = straddle (1/10) 4 ∧
    (splice (1/10) 4 5).lo = below (1/10) 4 ∧
    (splice (1/10) 4 5).hi = below (1/10) 4 := by
  simp [splice,QInterval.point]

theorem both_names_valid : Valid (straddle (1/10)) ((1/10:ℚ):ℝ) ∧
    Valid (splice (1/10) 4) (below (1/10) 4) :=
  ⟨straddle_valid _,splice_valid _ _⟩

theorem zero_fuel : run reader (straddle 1) 0 0 = none := rfl

theorem no_query_collision : run (fun _ : Unit => Sum.inl (1:ℤ)) (straddle (1/10)) 1 () =
    run (fun _ : Unit => Sum.inl (1:ℤ)) (splice (1/10) 0) 1 () := rfl

theorem canonical_boundary : DigitExtraction.digits 10 (1/10) 0 = 1 := decimal_boundary

theorem cf_boundary_and_below : (GenContFract.of (1:ℝ)).h = 1 ∧
    (GenContFract.of (below 1 4:ℝ)).h = 0 := by
  constructor
  · norm_num [cf_head]
  · rw [cf_head,(cf_below 4).2]; norm_num

def interior : QInterval := ⟨1/50,3/50,by norm_num⟩

theorem away_boundary_certificate (x : ℝ) (hx : interior.Contains x) :
    DigitExtraction.digits 10 x 0 = 0 := by
  exact floor_certificate interior x 10 0 hx (by norm_num)
    (by norm_num [interior]) (by norm_num [interior])

/-- Closing the upper endpoint at the digit boundary invalidates a cell proof. -/
theorem closed_boundary_control :
    (⟨0,1/10,by norm_num⟩ : QInterval).Contains (1/10) ∧
    DigitExtraction.digits 10 (1/10) 0 ≠ 0 := by
  norm_num [QInterval.Contains,DigitExtraction.digits,DigitExtraction.remainder]

#eval queries reader (straddle (1/10)) 4 0
#eval (run reader (straddle (1/10)) 4 0, run reader (splice (1/10) 4) 4 0)
#eval (below (1/10) 4, (splice (1/10) 4 5).lo, (splice (1/10) 4 5).hi)
#audit_namespace GeneralizedIntervalArithmetic.FiniteQueryChecks
end GeneralizedIntervalArithmetic.FiniteQueryChecks
