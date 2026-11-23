# Exact finite strict interval comparison

`StrictComparison.lean` gives a narrow Chapter 2 counterpart for Tupper
§2.7.2 (printed p.24 / PDF p.40) and the Boolean-interval interpretation in
§2.9.2 (printed p.27 / PDF p.43). Those two pages were visually checked against
the existing repository PDF copy. The source is Jeffrey Tupper,
[*Graphing Equations with Generalized Interval Arithmetic*](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=40)
(1996); no copy or transcription is needed by the build.

## Exact statement and witnesses

For ordered finite rational intervals `I=[a,b]`, `J=[c,d]`, interpreted over
reals, `compare` computes:

| Condition | Result | Actual Boolean outcomes |
| --- | --- | --- |
| `b < c` | `trueOnly` (T) | `{true}` |
| `d ≤ a` | `falseOnly` (F) | `{false}` |
| otherwise | `both` (TF) | `{false,true}` |

`compare_exact` proves equality of that set with
`{v | ∃ x y : ℝ, I.Contains x ∧ J.Contains y ∧ decide (x < y) = v}`.
The criterion theorems are iff statements. In the mixed case,
`both_witnesses` exhibits `(a,d)` for true and `(b,c)` for false, including
both membership obligations. Endpoint order is carried by `QInterval`.
The strict/weak distinction matters at touching endpoints.

`values_eq_Icc` identifies F, TF, T with `[false,false]`, `[false,true]`,
`[true,true]` in Boolean order. `Truth.Refines` is set inclusion;
`refines_iff` says `v` refines `w` precisely when they coincide or `w=both`.
`compare_refines` transports actual independent-domain inclusion to this
information order. It is distinct from the order false < true.

## Independence and scope

The independent witnesses are essential. For `I=J=[0,1]`, the comparison
has both outcomes; using the same real witness in `x<x` instead gives only
false. The fixture proves these outcome sets differ. A dual control uses `y=x+1`
on `[0,2]`: the correlated result is always true, whereas the independent
marginals `[0,2]` and `[1,3]` give both. Swapping strict comparisons does not
generally negate the result at equality. Malformed pairs such as `[2,0]` and
`[1,-1]` can satisfy both raw separation tests; their failed order obligations
prevent construction as `QInterval` inputs. This interface is not
`BranchDecision.unknown`, and no existing branch decision or evaluator changes.

Although TF can generally represent incomplete knowledge in the source, this
particular exact comparator proves both outcomes attainable in its independent
domain. That assertion must not be transferred to arbitrary conservative
Boolean bounds or correlated inputs. A value being enclosed is not in general
an existence certificate; here existence is proved explicitly.

This milestone does not cover the source's equality or greater-than examples
as new operators, Boolean composition, optimistic/pessimistic projection,
missing/exceptional endpoints, general partial comparisons, or a complete
three-valued algebra. The reference computation uses rational comparisons;
it does not implement native floating-point comparison or alter any approved
FP contract. The C API and all hardware/native paths are unchanged. There is
no runtime performance claim or renderer integration.

## Verification

[The fixture](tests/StrictComparison.lean) checks source-shaped `[1,3]` versus
`[4,6]` and `[2,4]`, touching/reverse-touching endpoints, equal singletons,
explicit mixed witnesses, refinement, and the correlated-input counterexample.
All declarations are covered by the enforced axiom policy.

```sh
lake build StrictComparison
lake env lean tests/StrictComparison.lean
./check.sh
```

See [VALIDATION.md](VALIDATION.md) for the actual full gate receipt and the
[Chapter 2 checklist](CHAPTER2_CHECKLIST.md) for deferred work. This branch is
independent of the separate exact image-hull PR; neither proof is a prerequisite
for the other.
