# Rational-expression family closure with explicit domains

Tupper §2.11.4, printed pp.35–36 / [PDF pp.51–52](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=52), describes total operations as retaining the conjunction of input constraints and partial operations as adding an operation-domain constraint. The printed page was visually rechecked. §2.13 uses existential piece membership at one parameter; §2.14's coefficient variants require care about the scope of coefficient choices. The persistent-choice convention used here is explicit, not inferred from equality of interval descriptions.

[RationalFamilyClosure.lean](RationalFamilyClosure.lean) closes a concrete multi-operation construction gap: it translates **every expression in the existing `Expr` grammar** (rational constants, two coordinates, addition, subtraction, multiplication and division) into a finite pair of rational multivariate polynomials plus a finite list of nonzero polynomial guards. It reuses `Expr.Value`, `GeneralFamilyDemotion`, `exactInputDomain`, the existing finite-piece denotation and the extended real-output hull. No new expression AST, partial-arithmetic semantics or native evaluator is introduced.

## Construction and exact theorem

A `Code` contains numerator `n`, denominator `d`, and guards `g₁,…,gₖ`. For each binary total operation, the construction concatenates the child guards and forms the ordinary cross-multiplied rational numerator/denominator. For division it also retains the divisor's numerator as a nonzero constraint. **Inherited guards are never canceled**, even when polynomial arithmetic cancels factors or makes the final denominator constant.

For one valuation `(x,y)`, `graph_exact` proves:

```
Value x y e z ↔ Admitted (compile e) x y ∧ z = n(x,y) / d(x,y).
```

`denominator_nonzero` proves that the generated guards imply `d(x,y) ≠ 0`; it does not assert the converse. `polynomial_graph_exact` therefore gives the equivalent finite polynomial graph equation `z*d(x,y) = n(x,y)` under the same guards. `domain_exact` proves that guard satisfaction is exactly existence of an actual semantic value. `division_domain` identifies the added condition with nonzero value of the actual divisor, not merely a test on an enclosing hull.

This is a mathematical finite-description construction. Mathlib's multivariate-polynomial operations make the current Lean translator `noncomputable`; it is **not an executable rational checker, quantifier eliminator or native hot path**. Real evaluation is also proof-side. The finite grammar and generated constraints are explicit; no arbitrary predicate oracle is introduced to assume the expression's domain. Existing input predicates may still encode externally supplied geometry.

## Families, pieces and demotion

`relation_exact` retains one original choice `w` at one parameter `p`, providing both coordinates `X p w` and `Y p w` for every occurrence. `outputs_exact` proves exact equality of the resulting sets of values for any admission predicate `A p w`. `classifications_exact` separately preserves both definite and possible domain classifications over those same choices. This stronger pointwise graph equivalence is important: image equality alone would not preserve universal definedness.

`pieces_exact` instantiates the construction with the existing finite half-space pieces and their open/closed boundary flags. The input witnesses are retained existentially alongside the polynomial graph. It does **not** eliminate them into the old affine half-space grammar, or treat the two coordinates as correlated unless the admission predicate specifies that relation. Independent coordinates are allowed by the piece-pair instance; repeated AST occurrences still share the chosen pair.

`family_hull_sound` reuses the established exact-output hull/demotion proof. It gives a sound enclosure and exact retained domain classifications, including empty or unbounded real images. The hull can fill image holes and is not claimed to be the actual image. An infinite bound is not a genuine infinity member or λ; this package introduces no exceptional arithmetic rows.

## Controls and obstruction

[Kernel-checked fixtures](tests/RationalFamilyClosure.lean) include:

- `1/(1/x)`: generated denominator is `1`, yet the inherited guard rejects `x=0`. Dropping old guards or checking only the final denominator would create a value.
- `0*(1/x)`: strict partiality still rejects zero input.
- `(x*x-1)/(x-1)`: agrees with `x+1` off `x=1`, while the canceled point remains absent.
- `1/(x*y-1)`: constructs the nonlinear domain condition `x*y ≠ 1` directly.
- A same-choice coefficient used in both coordinates makes `x-y=0`; independent re-choice admits `-1`. This is an exactness failure, not a refutation of conservative Cartesian enclosure.
- An existing finite band with `0 ≤ t < 1`, followed by `x/x`, has exact output `1` only for `0 < t < 1`. Both the operation hole and the external open boundary survive.
- Empty admitted choices are neither definitely nor possibly defined; mixed defined/undefined choices remain possible but not definite.
- No single affine function equals square even at `0`, `1/2` and `1`. Thus exact rational-expression closure does not imply closure of the single-affine representation. This control does not claim impossibility for every finite-piece or richer family.

## What this closes and what remains

The §2.11.4 conjunction/additional-domain rule now has a complete constructive mathematical counterpart for the existing strict rational-expression grammar, not only a result conditional on successful whole-hull guards. It also supplies exact same-witness graph transport through §2.13-style input unions and an enclosure via existing hulls. This is a deliberately specified rational-polynomial representation, not a claim that Tupper prescribed this particular syntax.

Remaining substantial work is **representation-specific elimination/demotion and property generation**, not another arithmetic guard lemma: extracting supported output pieces or finite endpoint bounds from these graphs, preserving classifications under such conversion, and handling source-supported operations outside the rational grammar. Roots, transcendental operations, arbitrary bumpy functions, literal exceptional coefficients, general weak/strong property tracking and unspecified source rows are not covered. The [closeout matrix](CHAPTER2_CLOSEOUT.md) retains these distinctions. No new proof or floating-point assumption, native/C/default change, runtime measurement or Chapter 2 completion claim is made.
