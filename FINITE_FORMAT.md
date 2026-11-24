# Literal finite formats and directed enclosure

[FiniteFormat.lean](FiniteFormat.lean) formalizes Tupper §2.5, printed p.18 /
PDF p.34: finite values `a*b^c`, integers `a,c`, with
`-b^(A-1) < a < b^(A-1)` and `m ≤ c+(A-1) ≤ M`.
The [original thesis](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=34)
was inspected visually using the repository source copy. We assume natural
radix `b ≥ 2`, positive natural precision `A`, and integer `m ≤ M`.

## Exact scope

`mem_values` proves that a finite rational enumeration represents exactly this
literal formula. Duplicate encodings denote one value. `finite_directed` proves
that an input bracketed by finite represented values has finite represented
lower/upper endpoints under existing `DiscreteDemotion.down/up`.
`enclosure_least` proves enclosure and containment in every represented finite
bracketing interval. `rational_down/up` identify these bounds from rational
extremum certificates. These are mathematical existence/extremality results,
not an implementation of real rounding.

`word_enclosure` connects the format hull to existing binary64 certificates:
both words must decode, both decoded rationals must separately belong to the
format, and they must enclose the actual output set. The theorem reuses hull
leastness; it does not assume equality of the two represented number families.

For §§2.9–2.10 this provides a concrete finite target for existing demotion.
[DiscreteDemotion](DiscreteDemotion.lean) already handles empty/unbounded real
output sets using mathematical infinite bounds; those are not format values or
an overflow policy. [Finite affine certification](FINITE_AFFINE_DEMOTION.md)
separately treats stored endpoints and outward evaluation at a shared parameter.
No new affine converter or optimality theorem is claimed.

## Source boundary

The adjacent printed p.19 unsigned digit presentation and its asserted
correspondence are not substituted for the coefficient formula. The literal
precision-one formula admits only zero, as checked in the fixtures. Its
correspondence with the digit presentation requires a sign/indexing/normalization
reconciliation. Likewise, this does not prove the source's stated binary64
format equals `Binary64.decode`'s image. These remain open source obligations.

No nearest/tie rule, subnormal or overflow policy is invented. There is no
native Float/Word bridge, encoder, automatic hardware success, ULP bound, native
path change or new FP assumption. The real-order extrema are noncomputable;
finite rational fixtures do not supply an arbitrary-real rounding algorithm.
Chapter 2 is not complete.

## Checks

[Kernel fixtures](tests/FiniteFormat.lean) prove decimal `(10,2,0,0)` gives
`0.35 → [0.3,0.4]`, includes its ±0.9 range edges and excludes 1; distinguish
binary and ternary membership; and check zero, precision one and a decoded-zero
Word bridge. No `native_decide` is used. Run `./check.sh` with the pinned
Lean/mathlib versions; the module and fixtures use the existing axiom allowlist.
