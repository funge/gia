# Directed demotion into finite rational value families

[DiscreteDemotion.lean](DiscreteDemotion.lean) constructs mathematical downward
and upward rounding for a finite rational value family, including a specialization
to the exact finite values of the existing binary64 decoder. It proves
representability, extremality and least outward interval enclosure; these are
conclusions, not an assumed rounding contract. No production converter or new
floating-point assumption is introduced.

## Source correspondence

Original PDF images were checked for Tupper §2.5.3 (printed p.20 / PDF p.36),
§2.6.2 (p.22 / PDF p.38), and §2.9.3's contrast between best scalar rounding and
non-optimal affine demotion (p.30 / PDF p.46):
[thesis](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=36).
The last passage explicitly characterizes downward scalar rounding as choosing
the largest available floating-point value no greater than the argument. The
proof implements that order-theoretic statement and its upward dual. Interval
projection reuses the actual-output infimum/supremum model of §§2.7.4–2.9.1.

This is a finite rational family, not the thesis's entire parametric F[b,A,m..M]
construction, nearest rounding/tie rule, exceptional arithmetic or affine
coefficient rounder. Existing integer-endpoint floor/ceil demotion remains in
NumberPromotion; it is not rewritten here. Scalar extremality here does not establish a best affine demotion.

## Model and exact guarantees

For `D : Finset ℚ`, `endpoints D` consists of its real-valued embeddings plus
ordered bound endpoints `⊥` and `⊤` in `EReal`. `down D x` is the maximum of
admissible endpoints ≤x; `up D x` is the minimum of endpoints ≥x. The added bounds
make both candidate sets nonempty, even when D is empty or x lies outside its
finite range. The construction is noncomputable mathematical finite selection
on real/extended bounds, not a practical rational-to-binary64 algorithm.

- `down_spec`/`up_spec` prove membership and outward order.
- `down_greatest`/`up_least` prove extremality; `down_eq`/`up_eq` give uniqueness
  from those properties. `fixed`/`fixed_iff` identify exact representability.
- Both maps are monotone and fix both infinite bounds.
- `hull D S` rounds the existing extended lower/upper hull of **actual real
  outputs** S. `sound` and `least` prove enclosure and leastness among all closed
  intervals whose endpoints lie in the target family.
- Empty S has canonical reversed bounds top/bottom and an empty denotation.
  Nonemptiness is preserved exactly. Unbounded sides retain the appropriate
  infinite bounds; finite nonempty bounded images have the explicit rounded
  `sInf`/`sSup` formula. No endpoint attainment is required.
- `relation_sound` preserves the actual input/output witness; enclosure does not
  manufacture values at holes or assert totality. Convexification may fill gaps
  as *enclosed possibilities*, not attained values.
- Refining the representable family tightens the least enclosure. If D⊆E,
  directed conversion through E then D equals direct conversion to D. This is
  conversion only, not rounded intermediate arithmetic, nearest rounding or
  an algebraic homomorphism.

`add_enclosed` connects the demotion to the already-proved endpoint attainment
of exact independent `QInterval.add`; no addition-soundness proof is replaced.

## Binary64 connection and trust boundary

`binaryValues` is the finite set of rationals returned by `Binary64.decode w`
for words below 2^64. `mem_binaryValues` proves precisely that membership
characterization, and `decoded_fixed` proves that every successfully decoded
value is fixed by these mathematical directional maps. NaNs, infinities and
oversized words do not decode to rational values. Bound infinities are added
separately; they are not obtained by decoding exceptional words.

The 2^64-word definition is **only a mathematical set**, not an enumeration to
run. It is kept irreducible to prevent accidental elaborator reduction; its
membership proof unfolds it symbolically. Both signed-zero words represent the
same rational zero, so the model does not choose or compare output zero bit
patterns. It proves no Word/native Float transport, flag behavior or hardware
rounding refinement.

`word_certificate` proves that any existing sound finite Word enclosure contains
the mathematical least representable hull. `observed_addition` discharges that
premise using the existing two observed CallSound hypotheses and successful
assembly theorem. Neither asserts the observed output equals the optimum or
that a call succeeds. A π fixture consumes the existing `Binary64.pi_contains`
certificate; it does not infer a new correctly rounded π operation or ULP result.

## Controls and genuine interpretation limits

[Kernel fixtures](tests/DiscreteDemotion.lean) cover exact representability,
a value strictly between endpoints, values outside the finite range, empty
images, an empty finite family, two-sided unbounded output and a one-sided
half-line. They also check nested-family conversion and a counterexample when
the nesting premise is removed: converting 1 via `{0,2}` then `{0,1}` rounds down
to 0, whereas direct conversion to `{0,1}` retains 1. Signed-zero numerical
collapse, malformed decoding and the existing π certificate are separate controls.

No new incompatible reading is selected. The pre-existing source questions
remain: numerical comparisons on exceptional values differ from reflexive bound
ordering; λ is not a bound; and “homomorphism” for F→R* cannot silently mean
preservation of rounded arithmetic. This module uses only the common
order-of-real-values/bounds portion. It does not settle those carrier/arithmetic
questions or add nearest-rounding rules. Those gaps remain on the Chapter 2 audit.

This belongs in the existing representation/extended-bound review unit (unit 2).
There is no production path or hardware integration in this milestone.
