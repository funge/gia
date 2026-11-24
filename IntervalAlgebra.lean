import IntervalOps

namespace GeneralizedIntervalArithmetic.IntervalAlgebra

/-- The existing four-corner product is contained in every closed interval
containing its four corners. This is an enclosure fact, not point attainment. -/
theorem product_corners_least (I J R : QInterval)
    (h00 : R.Contains ((I.lo:ℝ)*J.lo)) (h01 : R.Contains ((I.lo:ℝ)*J.hi))
    (h10 : R.Contains ((I.hi:ℝ)*J.lo)) (h11 : R.Contains ((I.hi:ℝ)*J.hi))
    {z : ℝ} (hz : (I.mul J).Contains z) : R.Contains z := by
  have hl : (R.lo:ℝ) ≤ (I.mul J).lo := by
    simpa [QInterval.mul] using le_min (le_min h00.1 h01.1) (le_min h10.1 h11.1)
  have hu : ((I.mul J).hi:ℝ) ≤ R.hi := by
    simpa [QInterval.mul] using max_le (max_le h00.2 h01.2) (max_le h10.2 h11.2)
  exact ⟨hl.trans hz.1,hz.2.trans hu⟩

/-- Tupper §2.7.5 (and real-interval §2.8): finite exact rational instance of
subdistributivity. This is not a theorem for arbitrary widening/rounding choices. -/
theorem subdistributive (I J K : QInterval) {z : ℝ}
    (hz : (I.mul (J.add K)).Contains z) :
    ((I.mul J).add (I.mul K)).Contains z := by
  have ilo : I.Contains I.lo := ⟨le_rfl,by exact_mod_cast I.ordered⟩
  have ihi : I.Contains I.hi := ⟨by exact_mod_cast I.ordered,le_rfl⟩
  have jlo : J.Contains J.lo := ⟨le_rfl,by exact_mod_cast J.ordered⟩
  have jhi : J.Contains J.hi := ⟨by exact_mod_cast J.ordered,le_rfl⟩
  have klo : K.Contains K.lo := ⟨le_rfl,by exact_mod_cast K.ordered⟩
  have khi : K.Contains K.hi := ⟨by exact_mod_cast K.ordered,le_rfl⟩
  have hc {a b c : ℝ} (ha : I.Contains a) (hb : J.Contains b) (hc : K.Contains c) :
      ((I.mul J).add (I.mul K)).Contains (a*(b+c)) := by
    simpa [mul_add] using add_encloses (mul_encloses ha hb) (mul_encloses ha hc)
  apply product_corners_least I (J.add K) _ _ _ _ _ hz
  · simpa [QInterval.add] using hc ilo jlo klo
  · simpa [QInterval.add] using hc ilo jhi khi
  · simpa [QInterval.add] using hc ihi jlo klo
  · simpa [QInterval.add] using hc ihi jhi khi

/-- Printed p.25's associative trail uses actual operand values. -/
theorem addition_trail {I J K : QInterval} {a b c : ℝ}
    (ha : I.Contains a) (hb : J.Contains b) (hc : K.Contains c) :
    (I.add (J.add K)).Contains ((a+b)+c) := by
  simpa [add_assoc] using add_encloses ha (add_encloses hb hc)

end GeneralizedIntervalArithmetic.IntervalAlgebra
