# Exceptional values: source correspondence and remaining limits

The original design recommendation below is retained as rationale; the current
proof status follows it. It is not a new axiom or a decision to migrate APIs. Sources were read in the
transcription and visually checked in the original thesis: §§2.5.1–2
(printed p.19 / [PDF p.35](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=35)),
§§2.6–2.6.3 (printed pp.21–22 / PDF pp.37–38), and §2.7.1 (printed p.23 /
PDF p.39). Existing §2.11 source checks are recorded in the concordance.

## Three layers must remain distinct

* **Source mathematical values and comparisons.** §2.6 defines R* as the reals
  plus two infinities. But §2.5.1's floating-point comparison explicitly returns
  false for equality of same-sign infinities, motivated by their representing
  unknown large real values. This comparison cannot be Lean's reflexive equality.
  §2.5.2 uses λ for undefined results and makes comparisons involving it false;
  it is not an extra real value. The asserted promotion F→R* needs qualification
  for λ, since the displayed R* carrier does not include it. Do not silently
  identify all these uses or infer a total homomorphism preserving every operation.
* **Existing GIA partial semantics.** `PartialRealArithmetic.divRel` requires a
  nonzero denominator; `SqrtValues` requires a nonnegative argument. Undefined
  inputs have no real-valued result. DomainBounds separates definite/possible
  definedness; unavailable range information is not an empty semantic domain.
  These translate the finite partial cases well, but do not encode source
  infinities, λ-valued comparison tables, or all exceptional arithmetic.
* **Native IEEE implementation boundary.** `Binary64.decode` deliberately maps
  both zeros to rational zero and rejects infinities, NaNs and oversized words.
  Its `none` is absence of a finite decoding, not a source λ tag. Hardware
  call failure is unknown, not proof of mathematical undefinedness. The approved
  finite directed-operation contract and empirical Float transport stay unchanged.
  No source exceptional comparison is adopted as an IEEE hardware rule here.

## Reuse and mismatch

Pinned mathlib [EReal.Basic](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Data/EReal/Basic.lean)
provides an ordered real carrier with top/bottom, suitable to investigate for
unbounded **bounds** and real embedding. Its equality is reflexive. Its totalized
arithmetic is not automatically a source partial-operation semantics:
[EReal.Inv](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Data/EReal/Inv.lean)
proves division by zero is zero, whereas our partial division has no value there.
Use explicit guarded relations rather than importing that behavior as a source law.
The finite package defines inequality by Boolean complement of real equality;
that identity must not automatically define λ/unordered comparison tables.

The source's §2.6.1 hyperreal discussion is a distinct survey/alternative-model
passage. It does not justify converting signed binary64 zeros into nonzero
infinitesimals in the existing real decoder. Likewise, ordered extended endpoints
used for a real-valued interval need not mean that infinity is itself an attainable
operator output. Keep these carrier and membership questions separate.

## Recommended next proof, without new FP assumptions

First build a small **bound-only correspondence**: embed actual real output sets
into an ordered extended-bound carrier; prove containment, least closed extended
hull and monotonicity, including unbounded and empty images; show agreement with
`ExactImageHull` when the image is nonempty and bounded. Represent emptiness
explicitly or prove that reversed bounds have empty real membership. No extended
addition/division or native infinity decoding is needed for this theorem.

Then separately specify source-labelled comparison relations and partial-operation
relations, with finite agreement lemmas. Never postulate nonreflexive Lean equality
or replace existing finite operations. Before claiming the whole §2.5/§2.6
correspondence, resolve how the source's representational comparison and its R*
carrier interact, and how λ participates in promotion. This is the genuine
semantic fork to review; using EReal for bounds alone does not settle it.

No choice here expands the IEEE trust boundary, changes production behavior or
asserts that the full source exceptional system has already been formalized.


## Current proof status

The recommended bound-only theorem is now implemented and locally qualified
in [ExtendedImageHull](EXTENDED_IMAGE_HULL.md), with empty images represented
by reversed top/bottom bounds and membership restricted to real outputs.
A separate mathlib hyperreal leaf supplies the source positive infinitesimal.
These results do not resolve the source comparison/lambda fork above, and do not change the IEEE contract. The explicitly supported arithmetic rows
are now documented in [exceptional arithmetic](EXCEPTIONAL_ARITHMETIC.md).


The [comparison subset](EXCEPTIONAL_COMPARISONS.md) now distinguishes
source `<` and `=` observations from structural equality and from bound ordering.
It leaves unmodeled cases explicit; the five-predicate source refinement below
qualifies the earlier lambda-reading question. This advances the common subset without resolving the full
promotion/arithmetic fork or changing any existing implementation contract.

Source refinement (2026-11-24): §2.1 printed p.15 / PDF p.31 explicitly names
five numerical comparisons (`<`, `≤`, `=`, `≥`, `>`), omitting `≠` despite its
use in the preceding formula. Printed p.14 / PDF p.30 uses `g(x) ≠ lambda`
as definedness. Both pages were visually checked. The ledger does not assert
a numerical `≠` table or a contradiction; sentinel tests remain distinct.
This narrows the earlier comparison question without changing its Lean subset.


The later [five-predicate continuation](EXCEPTIONAL_COMPARISONS.md) implements
all named finite/lambda rows and derives the supported non-strict/converse rows.
It preserves the original `<`/`=` observations, separates explicit from derived
source correspondence, and leaves mixed directions and promotion unresolved.
The original recommendation above is historical; ordered-bound foundations are
already proved and do not need to be rebuilt.
