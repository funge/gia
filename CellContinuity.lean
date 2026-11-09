import SemanticContinuity

namespace GeneralizedIntervalArithmetic

/-- Continuity on a closed cell is equivalent to continuity after its affine
unit reparameterization. Point cells are handled separately. -/
theorem parameter_cell_continuous_iff (C : ParameterCell) (g : ℝ → ℝ) :
    ContinuousOn g (Set.Icc (C.interval.lo:ℝ) C.interval.hi) ↔
    ContinuousOn (fun s => g (C.map s)) (Set.Icc (0:ℝ) 1) := by
  constructor
  · intro h
    exact h.comp (parameter_map_continuous C).continuousOn (fun _ hs => parameter_map_mem C hs)
  · intro h
    have ho : (C.interval.lo:ℝ) ≤ C.interval.hi := by exact_mod_cast C.interval.ordered
    rcases eq_or_lt_of_le ho with he | hp
    · rw [← he,Set.Icc_self]
      exact continuousOn_singleton g _
    · have hd : (0:ℝ) < C.interval.hi-C.interval.lo := sub_pos.mpr hp
      let r : ℝ → ℝ := fun t => (t-C.interval.lo)/(C.interval.hi-C.interval.lo)
      have cr : Continuous r := (continuous_id.sub continuous_const).div_const _
      have hr : ∀ t ∈ Set.Icc (C.interval.lo:ℝ) C.interval.hi, r t ∈ Set.Icc (0:ℝ) 1 := by
        intro t ht
        refine ⟨div_nonneg (sub_nonneg.mpr ht.1) hd.le,?_⟩
        exact (div_le_one hd).mpr (sub_le_sub_right ht.2 _)
      have hi (t : ℝ) : C.map (r t) = t := by
        unfold ParameterCell.map r
        field_simp
        nlinarith
      apply (h.comp cr.continuousOn hr).congr
      intro t _
      exact congrArg g (hi t).symm

private theorem closed_cell_union (cells : List ParameterCell) (g : ℝ → ℝ)
    (hl : ∀ C ∈ cells, ContinuousOn g (Set.Icc (C.interval.lo:ℝ) C.interval.hi)) :
    IsClosed {t : ℝ | ∃ C ∈ cells, C.interval.Contains t} ∧
    ContinuousOn g {t : ℝ | ∃ C ∈ cells, C.interval.Contains t} := by
  induction cells with
  | nil => simp only [List.not_mem_nil, false_and, exists_false, Set.setOf_false]
           exact ⟨isClosed_empty,continuousOn_empty g⟩
  | cons C cs ih =>
    have htail := ih (fun D hD => hl D (List.mem_cons_of_mem C hD))
    have he : {t : ℝ | ∃ D ∈ C::cs, D.interval.Contains t} =
        Set.Icc (C.interval.lo:ℝ) C.interval.hi ∪ {t : ℝ | ∃ D ∈ cs, D.interval.Contains t} := by
      ext t
      simp only [Set.mem_setOf_eq,List.mem_cons,Set.mem_union,Set.mem_Icc,QInterval.Contains]
      aesop
    rw [he]
    exact ⟨isClosed_Icc.union htail.1,
      ContinuousOn.union_isClosed isClosed_Icc htail.1 (hl C (by simp)) htail.2⟩

/-- A finite closed cover can glue restrictions of ONE common function.
Continuity includes shared boundaries; independent branch functions do not suffice. -/
theorem parameter_cover_continuous {cells : List ParameterCell} (hc : ParameterCover cells)
    {g : ℝ → ℝ}
    (hl : ∀ C ∈ cells, ContinuousOn (fun s => g (C.map s)) (Set.Icc (0:ℝ) 1)) :
    ContinuousOn g (Set.Icc (0:ℝ) 1) := by
  have hu := closed_cell_union cells g
    (fun C hC => (parameter_cell_continuous_iff C g).mpr (hl C hC))
  exact hu.2.mono (fun _ ht => hc _ ht)

/-- Local representatives must agree with the same global function everywhere
on each closed cell, including overlaps and endpoints. -/
theorem parameter_cover_continuous_of_agreement {cells : List ParameterCell}
    (hc : ParameterCover cells) {g : ℝ → ℝ} (f : ParameterCell → ℝ → ℝ)
    (hl : ∀ C ∈ cells, ContinuousOn (f C) (Set.Icc (0:ℝ) 1))
    (ha : ∀ C ∈ cells, ∀ s ∈ Set.Icc (0:ℝ) 1, f C s = g (C.map s)) :
    ContinuousOn g (Set.Icc (0:ℝ) 1) := by
  apply parameter_cover_continuous hc
  intro C hC
  exact (hl C hC).congr (fun s hs => (ha C hC s hs).symm)

end GeneralizedIntervalArithmetic
