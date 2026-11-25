# Exact output projection for guarded fractional-linear maps

Tupper §2.11.4 retains input constraints and adds partial-operation constraints;
§2.13.1, printed p.39 / [PDF p.55](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=55), defines interval-set inclusion at one shared parameter and illustrates why a reciprocal's two rays can be more useful than their whole-line hull. The original page image was visually rechecked. It does not give a general finite quantifier-elimination algorithm. This milestone supplies a **specific exact projection construction**, not such an algorithm or a new interpretation of exceptional values.

## Supported class and certificate

[FractionalProjection.lean](FractionalProjection.lean) builds on the guarded rational graphs from [RationalFamilyClosure.lean](RationalFamilyClosure.lean). For rational coefficients `a,b,c,d`, require:

- `a*d-b*c ≠ 0`;
- the polynomial identity `N*(c*x+d) = (a*x+b)*D`, where `N,D` are the existing expression's compiled numerator and denominator.

These are the `Certified` premises: concrete algebraic obligations checked by Lean, not an assumed semantic graph equality. The expression can be arbitrarily nested within the existing rational grammar and can have inherited guards depending on both coordinates. Cross-multiplication allows canceled factors; **it does not remove their guards**. Certificate generation is not automated here. A failed or missing certificate means this projection theorem is inapplicable, not that the expression has no values.

The class contains nonconstant affine maps, nonzero scalar reciprocals and all regular rational fractional-linear maps, including expressions whose rational value simplifies to one of them. Constant maps and general higher-degree maps do not satisfy this regularity condition in general. An everywhere-undefined expression may satisfy a vacuous polynomial identity; its inherited guards still exclude every value.

## Exact elimination, rather than only an existential description

Let `t` be the unchanged parameter/second coordinate, `z` the proposed output, and `cs` the existing finite union of rational affine half-space input pieces. Their open/closed flags and empty pieces are unchanged. The original image is:

```
∃ x, x ∈ pieces cs t ∧ Value x t e z.
```

For a certified map, `projection_exact` eliminates `x` in favor of the unique candidate

```
x = (d*z-b)/(a-c*z).
```

The output description consists of `a-c*z ≠ 0`, membership of this candidate in the original pieces at `t`, and **all original generated expression guards at that same `(x,t)`**. There is no remaining existential input in `Describes`. The proof works for arbitrary real `t,z`, not only rational queries. The finite determinant condition rules out a spurious solution at `a-c*z=0`; it does not assign an infinite output there.

`image_union` preserves existing finite unions. `image_inter` is exact for this certified class because two equal outputs force the very same original input. This intersection property is not claimed for arbitrary noninjective functions. `hull_encloses` reuses the existing closed extended-bound hull as an **overapproximation**, not an exact image or an endpoint-attainment claim.

This is a quantifier-free **rational-condition description** once the finite piece/guard conjunctions are expanded. No `IsSemialgebraic` theorem, general Tarski–Seidenberg result, polynomial sign solver, or automatic enumeration into interval pieces is claimed. The pinned project has no existing general projection theorem to reuse for that larger task. Rational conditions can motivate a later polynomial-sign representation, but that additional conversion is not silently assumed here.

## Proved effective rational query

`test` is an executable reference membership procedure for rational `t,z`:

1. Reject the missing inverse denominator.
2. Form the exact rational candidate `inverseQ`.
3. Run the existing finite-piece membership checker on `(t,inverseQ)`.
4. Run the **unchanged** exact rational singleton expression evaluator on `(inverseQ,t)` and test definedness.

The algorithm does not execute the noncomputable polynomial compiler. `test_exact` and `test_false_iff` prove true/false agreement with membership/nonmembership in the actual image over **all real input witnesses**, under `Certified`. Completeness is justified because the unique preimage of rational data is rational and the existing singleton evaluator is complete there. Thus false is an absence result for this certified query, not a reinterpretation of general interval-evaluator failure.

The raw function accepts coefficient data, but **its correctness theorem requires the certificate**. The degenerate constant-map control shows why callers must not treat an uncertified false as exclusion. This is proof-side rational reference execution, not a hardware binary64 path, performance result, or verification of Lean's native runtime. It introduces no new floating-point premise.

## Checked examples and limitations

[Fixtures](tests/FractionalProjection.lean) include:

- Reciprocal of `[-1,1]`: the exact image agrees with the existing two-ray theorem. Closed ray tips are retained, zero is excluded, and the convex hull admits zero anyway.
- Reciprocal of `(0,1]`: open input zero stays absent; finite outputs `1` and `2` are admitted. No genuine infinity or λ is inserted.
- `1/(1/x)`: value identity with the zero hole retained in the output.
- `(x*x-1)/(x-1)`: the canceled input `1` becomes a missing output `2`, although the simplified total affine function would include it.
- Adding `0*(1/y)` to that expression: the parameter hole `t=0` removes the whole output fiber despite unchanged simplified values elsewhere.
- `(2*x+1)/(x+1)`: exact all-input image is every real except `2`.
- Empty input pieces and a degenerate constant map that refutes an unconditional inverse-based checker.

Two `#eval` vectors exercise the actual reference route; separate kernel proofs establish the expected decisions. No benchmark, native/C/default change, or exceptional arithmetic extension is included.

The remaining output-conversion obligation is broader than this class: noninjective rational maps can have multiple candidate preimages, and general parameterized polynomial graphs need certified root/sign decomposition or another justified projection method. Producing explicit output interval pieces and then controlled demotion is still distinct from the exact descriptor/query proved here. Output membership does not determine universal input-definedness; retain the original admission/guard classification from the previous family result rather than infer source domain flags from a nonempty image. The [closeout matrix](CHAPTER2_CLOSEOUT.md) keeps Chapter 2 incomplete.
