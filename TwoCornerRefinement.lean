import TwoCornerDivision

namespace GeneralizedIntervalArithmetic.TwoCornerRefinement
open HardwareAddition HardwareMultiplication

/-- Inclusion of decoded real bounds; no assertion about raw representations. -/
def Refines {F : Type} (decode : F → Option ℝ) (new old : Bounds F) : Prop :=
  ∃ nl nu ol ou, decode new.lo = some nl ∧ decode new.hi = some nu ∧
    decode old.lo = some ol ∧ decode old.hi = some ou ∧ ol ≤ nl ∧ nu ≤ ou

theorem Refines.contains {F : Type} {decode : F → Option ℝ} {new old : Bounds F}
    (h : Refines decode new old) {z : ℝ} (hz : Contains decode new z) :
    Contains decode old z := by
  obtain ⟨nl,nu,ol,ou,hnl,hnu,hol,hou,hl,hu⟩ := h
  obtain ⟨a,b,ha,hb,hz⟩ := hz
  have ea : a = nl := Option.some.inj (ha.symm.trans hnl)
  have eb : b = nu := Option.some.inj (hb.symm.trans hnu)
  subst a; subst b
  exact ⟨ol,ou,hol,hou,hl.trans hz.1,hz.2.trans hu⟩

/-- Structural comparison under identical observed paired results. The new
lower uses the first (Down) endpoint and upper the second (Up) endpoint, exactly
as those observations occur in four-corner assembly. This is not a claim that
separate executions satisfying an enclosure contract produce identical outcomes. -/
theorem same_observations_refine {F : Type} {decode : F → Option ℝ}
    {chooseMin chooseMax : F → F → F}
    (hmin : SelectSound decode chooseMin min) (hmax : SelectSound decode chooseMax max)
    {ll lh hl hh lower upper : Option (F × F)} {old : Bounds F}
    {v₁ v₂ v₃ v₄ : ℝ}
    (h₁ : ResultSound decode ll v₁) (h₂ : ResultSound decode lh v₂)
    (h₃ : ResultSound decode hl v₃) (h₄ : ResultSound decode hh v₄)
    (hL : lower ∈ [ll,lh,hl,hh]) (hU : upper ∈ [ll,lh,hl,hh])
    (hold : assembleFour chooseMin chooseMax ll lh hl hh = some old) :
    ∃ new, assemble lower upper = some new ∧ Refines decode new old := by
  cases ll with
  | none => simp [assembleFour] at hold
  | some p₁ =>
    cases lh with
    | none => simp [assembleFour] at hold
    | some p₂ =>
      cases hl with
      | none => simp [assembleFour] at hold
      | some p₃ =>
        cases hh with
        | none => simp [assembleFour] at hold
        | some p₄ =>
          simp [assembleFour] at hold
          subst old
          obtain ⟨l₁,u₁,dl₁,du₁,_⟩ := h₁ p₁ rfl
          obtain ⟨l₂,u₂,dl₂,du₂,_⟩ := h₂ p₂ rfl
          obtain ⟨l₃,u₃,dl₃,du₃,_⟩ := h₃ p₃ rfl
          obtain ⟨l₄,u₄,dl₄,du₄,_⟩ := h₄ p₄ rfl
          have hol := hmin _ _ _ _ (hmin _ _ _ _ dl₁ dl₂) (hmin _ _ _ _ dl₃ dl₄)
          have hou := hmax _ _ _ _ (hmax _ _ _ _ du₁ du₂) (hmax _ _ _ _ du₃ du₄)
          have each (o : Option (F × F)) (ho : o ∈ [some p₁,some p₂,some p₃,some p₄]) :
              ∃ p l u, o = some p ∧ decode p.1 = some l ∧ decode p.2 = some u ∧
                min (min l₁ l₂) (min l₃ l₄) ≤ l ∧ u ≤ max (max u₁ u₂) (max u₃ u₄) := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
            rcases ho with rfl | rfl | rfl | rfl
            · exact ⟨p₁,l₁,u₁,rfl,dl₁,du₁,
                (min_le_left _ _).trans (min_le_left _ _),
                (le_max_left _ _).trans (le_max_left _ _)⟩
            · exact ⟨p₂,l₂,u₂,rfl,dl₂,du₂,
                (min_le_left _ _).trans (min_le_right _ _),
                (le_max_right _ _).trans (le_max_left _ _)⟩
            · exact ⟨p₃,l₃,u₃,rfl,dl₃,du₃,
                (min_le_right _ _).trans (min_le_left _ _),
                (le_max_left _ _).trans (le_max_right _ _)⟩
            · exact ⟨p₄,l₄,u₄,rfl,dl₄,du₄,
                (min_le_right _ _).trans (min_le_right _ _),
                (le_max_right _ _).trans (le_max_right _ _)⟩
          obtain ⟨lp,lo,_,hlo,dlo,_,hlo',_⟩ := each lower hL
          obtain ⟨up,_,hi,hhi,_,dhi,_,hhi'⟩ := each upper hU
          refine ⟨⟨lp.1,up.2⟩,?_,lo,hi,_,_,dlo,dhi,hol,hou,hlo',hhi'⟩
          simp [assemble,hlo,hhi]

/-- Decoded observations of the used directions. Failure/nonfinite decoding is
None, and equality here says nothing about raw tags or the unused pair sides. -/
def downValue {F : Type} (decode : F → Option ℝ) (r : Option (F × F)) : Option ℝ :=
  r.bind (fun p => decode p.1)
def upValue {F : Type} (decode : F → Option ℝ) (r : Option (F × F)) : Option ℝ :=
  r.bind (fun p => decode p.2)

theorem assembled_directions {F : Type} {decode : F → Option ℝ}
    {lower upper : Option (F × F)} {R : Bounds F} (h : assemble lower upper = some R) :
    downValue decode lower = decode R.lo ∧ upValue decode upper = decode R.hi := by
  cases lower <;> cases upper <;> simp_all [assemble,downValue,upValue]
  subst R
  exact ⟨rfl,rfl⟩

theorem assemble_decoded {F : Type} {decode : F → Option ℝ}
    {lower upper : Option (F × F)} {l u : ℝ}
    (hl : downValue decode lower = some l) (hu : upValue decode upper = some u) :
    ∃ R, assemble lower upper = some R ∧ decode R.lo = some l ∧ decode R.hi = some u := by
  cases lower with
  | none => cases hl
  | some lp =>
    cases upper with
    | none => cases hu
    | some up => exact ⟨⟨lp.1,up.2⟩,rfl,hl,hu⟩

/-- Weaker, direction-specific transfer: only the decoded Down of the new lower
call and decoded Up of the new upper call must agree. Those successful decoded
observations entail paired-result availability, but not unused-side equality.
Any enclosure already proved for mid transfers too. -/
theorem direction_transfer {F : Type} {decode : F → Option ℝ}
    {lower upper lower' upper' : Option (F × F)} {mid old : Bounds F}
    (hm : assemble lower upper = some mid) (href : Refines decode mid old)
    (hD : downValue decode lower' = downValue decode lower)
    (hU : upValue decode upper' = upValue decode upper) :
    ∃ new, assemble lower' upper' = some new ∧ Refines decode new old ∧
      ∀ z, Contains decode mid z ↔ Contains decode new z := by
  obtain ⟨l,u,ol,ou,dl,du,dol,dou,hl,hu⟩ := href
  obtain ⟨hmD,hmU⟩ := assembled_directions (decode := decode) hm
  obtain ⟨new,hn,dnl,dnu⟩ := assemble_decoded (hD.trans (hmD.trans dl)) (hU.trans (hmU.trans du))
  refine ⟨new,hn,⟨l,u,ol,ou,dnl,dnu,dol,dou,hl,hu⟩,?_⟩
  intro z
  constructor
  · intro hz
    exact (Refines.contains (show Refines decode mid new from
      ⟨l,u,l,u,dl,du,dnl,dnu,le_rfl,le_rfl⟩) hz)
  · intro hz
    exact (Refines.contains (show Refines decode new mid from
      ⟨l,u,l,u,dnl,dnu,dl,du,le_rfl,le_rfl⟩) hz)

/-- Four-call success plus identical *decoded used directions* suffices. This
requires no whole-pair or raw-representation equality for the new calls. -/
theorem directional_observations_refine {F : Type} {decode : F → Option ℝ}
    {chooseMin chooseMax : F → F → F}
    (hmin : SelectSound decode chooseMin min) (hmax : SelectSound decode chooseMax max)
    {ll lh hl hh lower upper lower' upper' : Option (F × F)} {old : Bounds F}
    {v₁ v₂ v₃ v₄ : ℝ}
    (h₁ : ResultSound decode ll v₁) (h₂ : ResultSound decode lh v₂)
    (h₃ : ResultSound decode hl v₃) (h₄ : ResultSound decode hh v₄)
    (hL : lower ∈ [ll,lh,hl,hh]) (hU : upper ∈ [ll,lh,hl,hh])
    (hD : downValue decode lower' = downValue decode lower)
    (hUp : upValue decode upper' = upValue decode upper)
    (hold : assembleFour chooseMin chooseMax ll lh hl hh = some old) :
    ∃ new, assemble lower' upper' = some new ∧ Refines decode new old := by
  obtain ⟨mid,hm,href⟩ := same_observations_refine hmin hmax h₁ h₂ h₃ h₄ hL hU hold
  obtain ⟨new,hn,hr,_⟩ := direction_transfer hm href hD hUp
  exact ⟨new,hn,hr⟩

/-- Operand/outcome associations prevent substituting a different call, even
when an implementation only promises enclosure and may return loose results. -/
def observations {F : Type} (I J : Bounds F)
    (ll lh hl hh : Option (F × F)) : List ((F × F) × Option (F × F)) :=
  [((I.lo,J.lo),ll),((I.lo,J.hi),lh),((I.hi,J.lo),hl),((I.hi,J.hi),hh)]

theorem observed_mem {F : Type} {I J : Bounds F} {ll lh hl hh out : Option (F × F)}
    {a b : F} (h : ((a,b),out) ∈ observations I J ll lh hl hh) : out ∈ [ll,lh,hl,hh] := by
  have hm : out ∈ (observations I J ll lh hl hh).map Prod.snd :=
    List.mem_map.mpr ⟨((a,b),out),h,rfl⟩
  simpa [observations] using hm

theorem observed_contract {F : Type} {decode : F → Option ℝ} {I J : Bounds F}
    {ll lh hl hh out : Option (F × F)} {a b : F}
    (hll : HardwareDivision.CallSound decode I.lo J.lo ll)
    (hlh : HardwareDivision.CallSound decode I.lo J.hi lh)
    (hhl : HardwareDivision.CallSound decode I.hi J.lo hl)
    (hhh : HardwareDivision.CallSound decode I.hi J.hi hh)
    (h : ((a,b),out) ∈ observations I J ll lh hl hh) :
    HardwareDivision.CallSound decode a b out := by
  simp only [observations,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h <;> cases h
  · exact hll
  · exact hlh
  · exact hhl
  · exact hhh

/-- On valid finite ordered intervals, a successful guarded four-call assembly
refines to a successful selected two-pair assembly under the same observations.
The real selection agreement and both operand/output direction agreements are
explicit. The conclusion includes mathematical enclosure, not raw-bit parity. -/
theorem guarded_refinement {F : Type} {decode : F → Option ℝ}
    {lt : F → F → Bool} {zero : F} {chooseMin chooseMax : F → F → F}
    (hcmp : HardwareDivision.CompareSound decode lt) (hz : decode zero = some 0)
    (hmin : SelectSound decode chooseMin min) (hmax : SelectSound decode chooseMax max)
    {I J old : Bounds F} {a b c d al bl au bu : ℝ}
    (ha : decode I.lo = some a) (hb : decode I.hi = some b)
    (hc : decode J.lo = some c) (hd : decode J.hi = some d)
    (_hab : a ≤ b) (hcd : c ≤ d) (hg : HardwareDivision.awayZero lt zero J = true)
    (hs : TwoCornerDivision.select a b c d = some ((al,bl),(au,bu)))
    {ln ld un ud : F} {ll lh hl hh lower upper : Option (F × F)}
    (hln : decode ln = some al) (hld : decode ld = some bl)
    (hun : decode un = some au) (hud : decode ud = some bu)
    (hll : HardwareDivision.CallSound decode I.lo J.lo ll)
    (hlh : HardwareDivision.CallSound decode I.lo J.hi lh)
    (hhl : HardwareDivision.CallSound decode I.hi J.lo hl)
    (hhh : HardwareDivision.CallSound decode I.hi J.hi hh)
    (hL : ((ln,ld),lower) ∈ observations I J ll lh hl hh)
    (hU : ((un,ud),upper) ∈ observations I J ll lh hl hh)
    (hold : HardwareDivision.assembleGuarded lt zero chooseMin chooseMax J ll lh hl hh = some old) :
    ∃ new, assemble lower upper = some new ∧ Refines decode new old ∧
      ∀ x y, Contains decode I x → Contains decode J y →
        Contains decode new (x/y) ∧ y ≠ 0 := by
  have guard := HardwareDivision.awayZero_sound hcmp hz hc hd hg
  have cn := HardwareDivision.guarded_nonzero guard ⟨le_rfl,hcd⟩
  have dn := HardwareDivision.guarded_nonzero guard ⟨hcd,le_rfl⟩
  have hold' : assembleFour chooseMin chooseMax ll lh hl hh = some old := by
    simpa [HardwareDivision.assembleGuarded,hg] using hold
  obtain ⟨new,hnew,href⟩ := same_observations_refine hmin hmax
    (hll a c ha hc cn) (hlh a d ha hd dn) (hhl b c hb hc cn) (hhh b d hb hd dn)
    (observed_mem hL) (observed_mem hU) hold'
  refine ⟨new,hnew,href,?_⟩
  intro x y hx hy
  obtain ⟨a',b',ha',hb',hx⟩ := hx
  obtain ⟨c',d',hc',hd',hy⟩ := hy
  have ea : a' = a := Option.some.inj (ha'.symm.trans ha)
  have eb : b' = b := Option.some.inj (hb'.symm.trans hb)
  have ec : c' = c := Option.some.inj (hc'.symm.trans hc)
  have ed : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst a'; subst b'; subst c'; subst d'
  exact TwoCornerDivision.assemble_selected_encloses hs hln hld hun hud
    (observed_contract hll hlh hhl hhh hL) (observed_contract hll hlh hhl hhh hU)
    hnew hx hy

end GeneralizedIntervalArithmetic.TwoCornerRefinement
