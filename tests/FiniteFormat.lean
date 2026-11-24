import FiniteFormat
import AuditPolicy
namespace GeneralizedIntervalArithmetic.FiniteFormatChecks
open FiniteFormat

def decimal : Format := ⟨10,2,0,0,by decide,by decide,by decide⟩
def binary : Format := ⟨2,2,0,0,by decide,by decide,by decide⟩
def ternary : Format := ⟨3,2,0,0,by decide,by decide,by decide⟩

theorem decimal_members : (3/10:ℚ) ∈ values decimal ∧ (4/10:ℚ) ∈ values decimal ∧
    (-(9/10):ℚ) ∈ values decimal ∧ (9/10:ℚ) ∈ values decimal := by
  norm_num [values, decimal, ternary, binary, bound, shift, value]

  exact ⟨⟨3,by norm_num,by norm_num⟩,⟨4,by norm_num,by norm_num⟩,⟨-9,by norm_num,by norm_num⟩,⟨9,by norm_num,by norm_num⟩⟩

theorem decimal_exclusions : (7/20:ℚ) ∉ values decimal ∧ (1:ℚ) ∉ values decimal := by
  norm_num [values, decimal, ternary, binary, bound, shift, value]

  constructor <;> intro x hx hy <;> interval_cases x <;> norm_num

theorem decimal_best :
    (∀ q ∈ values decimal, q ≤ (7/20:ℚ) → q ≤ 3/10) ∧
    (∀ q ∈ values decimal, (7/20:ℚ) ≤ q → 4/10 ≤ q) := by
  norm_num [values, decimal, ternary, binary, bound, shift, value]

  constructor <;> intro q x hx hy he hq <;> subst q <;> interval_cases x <;> norm_num at *

theorem decimal_directed :
    DiscreteDemotion.down (values decimal) ((7/20:ℚ):ℝ) = (((3/10:ℚ):ℝ):EReal) ∧
    DiscreteDemotion.up (values decimal) ((7/20:ℚ):ℝ) = (((4/10:ℚ):ℝ):EReal) :=
  ⟨rational_down decimal decimal_members.1 (by norm_num) decimal_best.1,
   rational_up decimal decimal_members.2.1 (by norm_num) decimal_best.2⟩

theorem radices_differ : (1/3:ℚ) ∈ values ternary ∧ (1/3:ℚ) ∉ values binary := by
  norm_num [values, decimal, ternary, binary, bound, shift, value]

  intro x hx hy
  interval_cases x <;> norm_num

theorem zero_fixed (F : Format) :
    DiscreteDemotion.down (values F) 0 = 0 ∧ DiscreteDemotion.up (values F) 0 = 0 := by
  apply DiscreteDemotion.fixed
  exact (DiscreteDemotion.mem_endpoints _ _).mpr (Or.inr (Or.inr ⟨0,zero_mem F,by norm_num⟩))

theorem in_range : InRange decimal (7/20) :=
  ⟨3/10,decimal_members.1,4/10,decimal_members.2.1,by norm_num,by norm_num⟩

theorem finite_output : ∃ l ∈ values decimal, ∃ u ∈ values decimal,
    DiscreteDemotion.down (values decimal) ((7/20:ℝ):EReal) = ((l:ℝ):EReal) ∧
    DiscreteDemotion.up (values decimal) ((7/20:ℝ):EReal) = ((u:ℝ):EReal) ∧
    (l:ℝ) ≤ 7/20 ∧ (7/20:ℝ) ≤ (u:ℝ) := finite_directed decimal in_range

theorem one_out_of_range : ¬ InRange decimal 1 := by
  rintro ⟨l,hl,u,hu,_,h⟩
  have hb : ∀ q ∈ values decimal, q ≤ (9/10:ℚ) := by
    norm_num [values, decimal, bound, shift, value]
    intro q x hx hy he
    subst q
    interval_cases x <;> norm_num
  have hh : (u:ℝ) ≤ (9/10:ℚ) := by exact_mod_cast hb u hu
  norm_num at hh
  linarith

theorem range_edges : InRange decimal (9/10) ∧ InRange decimal (-(9/10)) := by
  constructor
  · exact ⟨9/10,decimal_members.2.2.2,9/10,decimal_members.2.2.2,by norm_num,by norm_num⟩
  · exact ⟨-(9/10),decimal_members.2.2.1,-(9/10),decimal_members.2.2.1,by norm_num,by norm_num⟩

/-- The coefficient bound is strict: the literal A=1 format has only zero.
This does not assert equivalence to the adjacent unsigned digit description. -/
def oneDigit : Format := ⟨10,1,0,0,by decide,by decide,by decide⟩
theorem one_digit_literal : ∀ q ∈ values oneDigit, q = 0 := by
  norm_num [values, oneDigit, bound, shift, value]
  intro q a ha hb he
  have : a=0 := by omega
  subst a
  simpa using he.symm

theorem zero_word_bridge : ∀ x ∈ DiscreteDemotion.hull (values decimal) {0},
    HardwareAddition.Contains Binary64.real ⟨0,0⟩ x := by
  apply word_enclosure decimal (a:=0) (b:=0)
  · norm_num [Binary64.decode, Binary64.exponent, Binary64.fraction, Binary64.sign]
  · norm_num [Binary64.decode, Binary64.exponent, Binary64.fraction, Binary64.sign]
  · exact zero_mem decimal
  · exact zero_mem decimal
  · intro x hx
    have h : x=0 := by simpa using hx
    subst x
    norm_num

end GeneralizedIntervalArithmetic.FiniteFormatChecks
#audit_namespace GeneralizedIntervalArithmetic.FiniteFormatChecks
