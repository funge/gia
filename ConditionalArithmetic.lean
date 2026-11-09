import ConditionalEvaluator

namespace GeneralizedIntervalArithmetic

/-- Apply an arithmetic expression transformation to every leaf, retaining guards. -/
def ConditionalExpr.mapLeaves (f : Expr → Expr) : ConditionalExpr → ConditionalExpr
  | .leaf e => .leaf (f e)
  | .iteLt g q a b => .iteLt g q (a.mapLeaves f) (b.mapLeaves f)

/-- Distribute strict binary arithmetic through both trees, without sharing. -/
def ConditionalExpr.liftBinary (f : Expr → Expr → Expr) :
    ConditionalExpr → ConditionalExpr → ConditionalExpr
  | .leaf e, b => b.mapLeaves (f e)
  | .iteLt g q a b, c => .iteLt g q (a.liftBinary f c) (b.liftBinary f c)

theorem conditional_ite_iff {x y z : ℝ} {g : Expr} {q : ℚ} {a b : ConditionalExpr} :
    ConditionalValue x y (.iteLt g q a b) z ↔
      ∃ u, Value x y g u ∧
        ((u < (q:ℝ) ∧ ConditionalValue x y a z) ∨
         ((q:ℝ) ≤ u ∧ ConditionalValue x y b z)) := by
  constructor
  · intro h
    cases h with
    | yes hg hlt ha => exact ⟨_,hg,Or.inl ⟨hlt,ha⟩⟩
    | no hg hle hb => exact ⟨_,hg,Or.inr ⟨hle,hb⟩⟩
  · rintro ⟨u,hg,h⟩
    rcases h with ⟨hlt,ha⟩ | ⟨hle,hb⟩
    · exact ConditionalValue.yes hg hlt ha
    · exact ConditionalValue.no hg hle hb

/-- Exact semantic correspondence, including the domain, for leaf mapping. -/
theorem conditional_map_iff {x y : ℝ} {f : Expr → Expr} {R : ℝ → ℝ → Prop}
    (hf : ∀ e z, Value x y (f e) z ↔ ∃ v, Value x y e v ∧ R v z)
    (a : ConditionalExpr) (z : ℝ) :
    ConditionalValue x y (a.mapLeaves f) z ↔ ∃ v, ConditionalValue x y a v ∧ R v z := by
  induction a generalizing z with
  | leaf e => simpa only [ConditionalExpr.mapLeaves,conditional_leaf_iff] using hf e z
  | iteLt g q a b iha ihb =>
    simp only [ConditionalExpr.mapLeaves,conditional_ite_iff,iha,ihb]
    aesop

/-- Both operands have values at the same coordinates. Preserve the leaf
operation's partial relation exactly, not merely its enclosure. -/
theorem conditional_liftBinary_iff {x y : ℝ} {f : Expr → Expr → Expr}
    {R : ℝ → ℝ → ℝ → Prop}
    (hf : ∀ e d z, Value x y (f e d) z ↔
      ∃ u v, Value x y e u ∧ Value x y d v ∧ R u v z)
    (a b : ConditionalExpr) (z : ℝ) :
    ConditionalValue x y (a.liftBinary f b) z ↔
      ∃ u v, ConditionalValue x y a u ∧ ConditionalValue x y b v ∧ R u v z := by
  induction a generalizing z with
  | leaf e =>
    simp only [ConditionalExpr.liftBinary,conditional_leaf_iff]
    have hm := conditional_map_iff (x := x) (y := y) (f := f e)
      (R := fun v z => ∃ u, Value x y e u ∧ R u v z)
      (by intro d z; rw [hf]; aesop) b z
    rw [hm]
    aesop
  | iteLt g q a c iha ihc =>
    simp only [ConditionalExpr.liftBinary,conditional_ite_iff,iha,ihc]
    constructor
    · rintro ⟨w,hw,h⟩
      rcases h with ⟨hlt,u,v,hu,hv,hr⟩ | ⟨hle,u,v,hu,hv,hr⟩
      · exact ⟨u,v,⟨w,hw,Or.inl ⟨hlt,hu⟩⟩,hv,hr⟩
      · exact ⟨u,v,⟨w,hw,Or.inr ⟨hle,hu⟩⟩,hv,hr⟩
    · rintro ⟨u,v,⟨w,hw,h⟩,hv,hr⟩
      rcases h with ⟨hlt,hu⟩ | ⟨hle,hu⟩
      · exact ⟨w,hw,Or.inl ⟨hlt,u,v,hu,hv,hr⟩⟩
      · exact ⟨w,hw,Or.inr ⟨hle,u,v,hu,hv,hr⟩⟩

inductive ArithmeticOp where
  | add | sub | mul | div

def ArithmeticOp.expr : ArithmeticOp → Expr → Expr → Expr
  | .add => Expr.add
  | .sub => Expr.sub
  | .mul => Expr.mul
  | .div => Expr.div

/-- Division has an explicit nonzero premise, independent of totalized real division. -/
def ArithmeticOp.Rel : ArithmeticOp → ℝ → ℝ → ℝ → Prop
  | .add, u,v,z => z = u+v
  | .sub, u,v,z => z = u-v
  | .mul, u,v,z => z = u*v
  | .div, u,v,z => v ≠ 0 ∧ z = u/v

theorem arithmeticOp_value_iff (op : ArithmeticOp) (x y : ℝ) (e d : Expr) (z : ℝ) :
    Value x y (op.expr e d) z ↔
      ∃ u v, Value x y e u ∧ Value x y d v ∧ op.Rel u v z := by
  cases op <;> constructor
  all_goals simp only [ArithmeticOp.expr, ArithmeticOp.Rel] at *
  · intro h; cases h with | add ha hb => exact ⟨_,_,ha,hb,rfl⟩
  · rintro ⟨u,v,hu,hv,rfl⟩; exact Value.add hu hv
  · intro h; cases h with | sub ha hb => exact ⟨_,_,ha,hb,rfl⟩
  · rintro ⟨u,v,hu,hv,rfl⟩; exact Value.sub hu hv
  · intro h; cases h with | mul ha hb => exact ⟨_,_,ha,hb,rfl⟩
  · rintro ⟨u,v,hu,hv,rfl⟩; exact Value.mul hu hv
  · intro h; cases h with | div ha hb hn => exact ⟨_,_,ha,hb,hn,rfl⟩
  · rintro ⟨u,v,hu,hv,hn,rfl⟩; exact Value.div hu hv hn

/-- Strict partial arithmetic, independently of compilation. -/
def ConditionalArithmeticValue (x y : ℝ) (op : ArithmeticOp)
    (a b : ConditionalExpr) (z : ℝ) : Prop :=
  ∃ u v, ConditionalValue x y a u ∧ ConditionalValue x y b v ∧ op.Rel u v z

def arithmeticTree (op : ArithmeticOp) (a b : ConditionalExpr) : ConditionalExpr :=
  a.liftBinary op.expr b

theorem arithmeticTree_value_iff (x y : ℝ) (op : ArithmeticOp)
    (a b : ConditionalExpr) (z : ℝ) :
    ConditionalValue x y (arithmeticTree op a b) z ↔ ConditionalArithmeticValue x y op a b z :=
  conditional_liftBinary_iff (arithmeticOp_value_iff op x y) a b z

def evalConditionalArithmetic (X Y : LinearInterval) (op : ArithmeticOp)
    (a b : ConditionalExpr) : Option LinearInterval :=
  evalConditional X Y (arithmeticTree op a b)

/-- Exact compatibility with the old guarded arithmetic evaluator on leaves. -/
theorem evalConditionalArithmetic_leaves (X Y : LinearInterval) (op : ArithmeticOp)
    (a b : Expr) :
    evalConditionalArithmetic X Y op (.leaf a) (.leaf b) = evalGuarded X Y (op.expr a b) := rfl

theorem evalConditionalArithmetic_sound {X Y R : LinearInterval} {t x y z : ℝ}
    {op : ArithmeticOp} {a b : ConditionalExpr}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hv : ConditionalArithmeticValue x y op a b z)
    (hr : evalConditionalArithmetic X Y op a b = some R) : R.Contains t z :=
  evalConditional_sound ht hx hy ((arithmeticTree_value_iff x y op a b z).mpr hv) hr

theorem evalConditionalArithmetic_defined {X Y R : LinearInterval} {t x y : ℝ}
    {op : ArithmeticOp} {a b : ConditionalExpr}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : X.Contains t x) (hy : Y.Contains t y)
    (hr : evalConditionalArithmetic X Y op a b = some R) :
    ∃ z, ConditionalArithmeticValue x y op a b z := by
  obtain ⟨z,hz⟩ := evalConditional_defined ht hx hy hr
  exact ⟨z,(arithmeticTree_value_iff x y op a b z).mp hz⟩

/-- Carry the exact arithmetic relation through the existing coordinate-domain contract. -/
theorem evalConditionalArithmetic_relational_sound
    {X Y R : LinearInterval} {D E : DomainBounds ℝ} {A B : ℝ → ℝ → Prop}
    {op : ArithmeticOp} {a b : ConditionalExpr}
    (hX : (X.onDomain D).Sound A) (hY : (Y.onDomain E).Sound B)
    (hr : evalConditionalArithmetic X Y op a b = some R) :
    (R.onDomain (D.inter E)).Sound
      (fun t z => ∃ x y, A t x ∧ B t y ∧ ConditionalArithmeticValue x y op a b z) := by
  have hc := evalConditional_relational_sound hX hY hr
  refine ⟨?_,?_,?_⟩
  · rintro t z ⟨x,y,hx,hy,hv⟩
    exact hc.1 t z ⟨x,y,hx,hy,(arithmeticTree_value_iff x y op a b z).mpr hv⟩
  · rintro t z ⟨x,y,hx,hy,hv⟩
    exact hc.2.1 t z ⟨x,y,hx,hy,(arithmeticTree_value_iff x y op a b z).mpr hv⟩
  · intro t ht
    obtain ⟨z,x,y,hx,hy,hv⟩ := hc.2.2 t ht
    exact ⟨z,x,y,hx,hy,(arithmeticTree_value_iff x y op a b z).mp hv⟩

end GeneralizedIntervalArithmetic
