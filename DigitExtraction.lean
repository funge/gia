import DigitRepresentations

/-! Tupper §2.15.3: mathematical extraction and canonical digit correspondence.
Real floor is not an executable oracle for arbitrary real inputs. -/
namespace GeneralizedIntervalArithmetic.DigitExtraction
open DigitRepresentations Filter
open scoped Topology BigOperators

noncomputable def remainder (b : ℕ) (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n+1 => Int.fract ((b:ℝ) * remainder b x n)

noncomputable def digits (b : ℕ) (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(b:ℝ) * remainder b x n⌋

def Ordinary (b : ℕ) (d : ℕ → ℤ) : Prop := ∀n, 0≤d n ∧ d n<b

/-- Excludes precisely an eventually maximal-digit tail, not arbitrary redundancy. -/
def Canonical (b : ℕ) (d : ℕ → ℤ) : Prop := ∀N, ∃n, N≤n ∧ d n < (b:ℤ)-1

theorem remainder_range (b : ℕ) {x : ℝ} (hx : x∈Set.Ico 0 1) (n : ℕ) :
    remainder b x n ∈ Set.Ico 0 1 := by
  cases n with
  | zero => exact hx
  | succ n => exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem digits_ordinary {b : ℕ} (hb : 2≤b) {x : ℝ} (hx : x∈Set.Ico 0 1) :
    Ordinary b (digits b x) := by
  intro n
  have hr := remainder_range b hx n
  have hp : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
  constructor
  · exact Int.floor_nonneg.mpr (mul_nonneg hp.le hr.1)
  · change ⌊(b:ℝ)*remainder b x n⌋ < (b:ℤ)
    apply Int.floor_lt.mpr
    push_cast
    nlinarith [hr.2]

theorem ordinary_bound {b : ℕ} {d : ℕ → ℤ} (hd : Ordinary b d) :
    ∀n, |d n| ≤ (b:ℤ)-1 := by
  intro n; rw [abs_of_nonneg (hd n).1]; have := (hd n).2; omega

theorem digit_step (b : ℕ) (x : ℝ) (n : ℕ) :
    (digits b x n:ℝ) + remainder b x (n+1) = (b:ℝ)*remainder b x n := by
  exact Int.floor_add_fract _

theorem partial_remainder {b : ℕ} (hb : 2≤b) (x : ℝ) (N : ℕ) :
    (partialSum (digits b x) b N : ℝ) + remainder b x N * ((b:ℝ)⁻¹)^N = x := by
  have hne : (b:ℝ)≠0 := by positivity
  induction N with
  | zero => simp [partialSum,remainder]
  | succ N ih =>
    have hs : (partialSum (digits b x) b (N+1):ℝ) =
        (partialSum (digits b x) b N:ℝ) + (digits b x N:ℝ)*((b:ℝ)⁻¹)^(N+1) := by
      simp [partialSum,Finset.sum_range_succ]
    rw [hs,pow_succ]
    have ht := digit_step b x N
    calc
      _ = (partialSum (digits b x) b N:ℝ) +
          ((digits b x N:ℝ)+remainder b x (N+1))*((b:ℝ)⁻¹)^N*(b:ℝ)⁻¹ := by ring
      _ = _ := by
        rw [ht]
        calc
          _ = (partialSum (digits b x) b N:ℝ) + remainder b x N*((b:ℝ)⁻¹)^N := by field_simp; ring
          _ = x := ih

theorem extraction_exact {b : ℕ} (hb : 2≤b) {x : ℝ} (hx : x∈Set.Ico 0 1) :
    value (digits b x) b = x := by
  have hp : (1:ℝ)<b := by exact_mod_cast (show 1<b by omega)
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0≤(b:ℝ)⁻¹)
    ((inv_lt_one₀ (by positivity)).mpr hp)
  have hr : Tendsto (fun N => remainder b x N*((b:ℝ)⁻¹)^N) atTop (𝓝 0) := by
    apply squeeze_zero (fun N => mul_nonneg (remainder_range b hx N).1 (by positivity))
      (fun N => ?_) hg
    exact (mul_le_mul_of_nonneg_right (remainder_range b hx N).2.le (by positivity)).trans_eq (one_mul _)
  have hlim : Tendsto (fun N => (partialSum (digits b x) b N:ℝ)) atTop (𝓝 x) := by
    have h := (tendsto_const_nhds (x:=x)).sub hr
    simp only [sub_zero] at h
    convert h using 1
    funext N; linarith [partial_remainder hb x N]
  exact tendsto_nhds_unique (partial_represents hb (ordinary_bound (digits_ordinary hb hx))) hlim



theorem value_lt_one_iff {b : ℕ} (hb : 2≤b) {d : ℕ → ℤ} (hd : Ordinary b d) :
    value d b < 1 ↔ ∃n, d n < (b:ℤ)-1 := by
  constructor
  · intro h
    by_contra hn
    have he : d = fun _ => (b:ℤ)-1 := by
      funext n
      have hn' : ¬d n < (b:ℤ)-1 := fun hn' => hn ⟨n,hn'⟩
      have := hd n
      omega
    rw [he,maximal_digits hb] at h
    exact (lt_irrefl _) h
  · rintro ⟨n,hn⟩
    have hl : term d b ≤ fun k => ((b:ℝ)-1)*((b:ℝ)⁻¹)^(k+1) := by
      intro k
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show d k ≤ (b:ℤ)-1 by have := hd k; omega)
    have hs : term d b n < ((b:ℝ)-1)*((b:ℝ)⁻¹)^(n+1) := by
      apply mul_lt_mul_of_pos_right _ (by positivity)
      exact_mod_cast hn
    have h := Summable.tsum_lt_tsum hl hs (summable hb (ordinary_bound hd))
      (geometric_majorant hb).summable
    rw [(geometric_majorant hb).tsum_eq] at h
    exact h

theorem canonical_iff_tails {b : ℕ} (hb : 2≤b) {d : ℕ → ℤ} (hd : Ordinary b d) :
    Canonical b d ↔ ∀N, value (fun n => d (N+n)) b < 1 := by
  constructor
  · intro h N
    apply (value_lt_one_iff hb (fun n => hd (N+n))).2
    obtain ⟨n,hn,hv⟩ := h N
    exact ⟨n-N,by simpa [Nat.add_sub_of_le hn] using hv⟩
  · intro h N
    obtain ⟨n,hn⟩ := (value_lt_one_iff hb (fun n => hd (N+n))).1 (h N)
    exact ⟨N+n,by omega,hn⟩

theorem remainder_add (b : ℕ) (x : ℝ) (N k : ℕ) :
    remainder b x (N+k) = remainder b (remainder b x N) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Int.fract ((b:ℝ)*remainder b x (N+k)) = _
    rw [ih]
    rfl

theorem extracted_tail (b : ℕ) (x : ℝ) (N : ℕ) :
    (fun n => digits b x (N+n)) = digits b (remainder b x N) := by
  funext n
  simp only [digits,remainder_add]

theorem extracted_canonical {b : ℕ} (hb : 2≤b) {x : ℝ} (hx : x∈Set.Ico 0 1) :
    Canonical b (digits b x) := by
  apply (canonical_iff_tails hb (digits_ordinary hb hx)).2
  intro N
  rw [extracted_tail,extraction_exact hb (remainder_range b hx N)]
  exact (remainder_range b hx N).2

theorem value_step {b : ℕ} (hb : 2≤b) {d : ℕ → ℤ} (hd : Ordinary b d) :
    (b:ℝ)*value d b = (d 0:ℝ) + value (fun n => d (n+1)) b := by
  have hs := (summable hb (ordinary_bound hd)).sum_add_tsum_nat_add 1
  have ht : (fun n => term d b (n+1)) =
      fun n => (b:ℝ)⁻¹ * term (fun n => d (n+1)) b n := by
    funext n; simp only [term,pow_succ]; ring
  have hb0 : (b:ℝ)≠0 := by positivity
  unfold value
  rw [←hs,ht,tsum_mul_left]
  simp only [Finset.sum_range_one,term,zero_add,pow_one]
  field_simp

theorem reconstruct {b : ℕ} (hb : 2≤b) {d : ℕ → ℤ} (hd : Ordinary b d)
    (hc : Canonical b d) : digits b (value d b) = d := by
  have ht := (canonical_iff_tails hb hd).1 hc
  have hr : ∀N, remainder b (value d b) N = value (fun n => d (N+n)) b := by
    intro N
    induction N with
    | zero => simp [remainder]
    | succ N ih =>
      have hs := value_step hb (fun n => hd (N+n))
      have he : (fun n => d (N+(n+1))) = (fun n => d ((N+1)+n)) := by
        funext n; congr 1; omega
      simp only [Nat.add_zero,he] at hs
      have hf : ⌊(b:ℝ)*value (fun n=>d (N+n)) b⌋ = d N := by
        apply Int.floor_eq_iff.mpr
        have hz := (ordinary_range hb (fun n => hd ((N+1)+n))).1
        constructor <;> linarith [ht (N+1)]
      simp only [remainder,ih,Int.fract,hf]
      linarith
  funext N
  unfold digits
  rw [hr]
  apply Int.floor_eq_iff.mpr
  have hs := value_step hb (fun n => hd (N+n))
  have he : (fun n => d (N+(n+1))) = (fun n => d ((N+1)+n)) := by
    funext n; congr 1; omega
  simp only [Nat.add_zero,he] at hs
  have hz := (ordinary_range hb (fun n => hd ((N+1)+n))).1
  constructor <;> linarith [ht (N+1)]

theorem canonical_unique {b : ℕ} (hb : 2≤b) {d e : ℕ → ℤ}
    (hd : Ordinary b d) (he : Ordinary b e) (hc : Canonical b d) (hf : Canonical b e) :
    value d b = value e b ↔ d=e := by
  constructor
  · intro h
    rw [←reconstruct hb hd hc, h,reconstruct hb he hf]
  · rintro rfl; rfl

/-- All real magnitudes, including negatives and integers, via an integer part.
This fixed radix-point convention is explicit; it does not claim uniqueness of
arbitrary floating-place/sign encodings. -/
theorem all_real (b : ℕ) (hb : 2≤b) (x : ℝ) :
    ∃a : ℤ, ∃d : ℕ→ℤ, Ordinary b d ∧ Canonical b d ∧ x = (a:ℝ)+value d b := by
  have hx : Int.fract x ∈ Set.Ico (0:ℝ) 1 := ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  refine ⟨⌊x⌋,digits b (Int.fract x),digits_ordinary hb hx,extracted_canonical hb hx,?_⟩
  rw [extraction_exact hb hx]
  exact (Int.floor_add_fract x).symm



theorem canonical_range {b : ℕ} (hb : 2≤b) {d : ℕ→ℤ}
    (hd : Ordinary b d) (hc : Canonical b d) : value d b ∈ Set.Ico 0 1 := by
  refine ⟨(ordinary_range hb hd).1,?_⟩
  simpa using (canonical_iff_tails hb hd).1 hc 0

theorem integer_part {b : ℕ} (hb : 2≤b) (a : ℤ) {d : ℕ→ℤ}
    (hd : Ordinary b d) (hc : Canonical b d) : ⌊(a:ℝ)+value d b⌋=a := by
  apply Int.floor_eq_iff.mpr
  have h := canonical_range hb hd hc
  constructor <;> linarith [h.1,h.2]

theorem representation_unique {b : ℕ} (hb : 2≤b) (a c : ℤ) {d e : ℕ→ℤ}
    (hd : Ordinary b d) (he : Ordinary b e) (hc : Canonical b d) (hf : Canonical b e) :
    (a:ℝ)+value d b = (c:ℝ)+value e b ↔ a=c ∧ d=e := by
  constructor
  · intro h
    have ha := congrArg Int.floor h
    rw [integer_part hb a hd hc,integer_part hb c he hf] at ha
    refine ⟨ha,(canonical_unique hb hd he hc hf).1 ?_⟩
    simpa [ha] using h
  · rintro ⟨rfl,rfl⟩; rfl

theorem zero_remainder (b : ℕ) (n : ℕ) : remainder b 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [remainder,ih]

theorem zero_digits (b : ℕ) : digits b 0 = fun _ => 0 := by
  funext n; simp [digits,zero_remainder]

theorem terminating_tail (b : ℕ) (x : ℝ) (N : ℕ) (h : remainder b x N=0) :
    ∀n, digits b x (N+n)=0 := by
  intro n
  have he := congrFun (extracted_tail b x N) n
  simpa [h,zero_digits] using he

end GeneralizedIntervalArithmetic.DigitExtraction
