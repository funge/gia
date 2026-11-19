# Narrow syntax-directed residue inference

[ResidueInference.lean](ResidueInference.lean) automates a small part of
[integer residue certificates](INTEGER_RESIDUE.md). This is a new, tiny
**proof-side syntax**, not a modification of a production AST or evaluator.
The existing `Evaluator.Expr` has no floor constructor. No parser, runtime,
C/hardware arithmetic or renderer is connected here.

## Syntax and contract

Expressions contain exact integer constants, opaque partial real leaves, floor,
addition, subtraction, and scaling by an exact integer. A leaf is interpreted by
a client relation `R atom parameter value`. All children use the same parameter;
actual value witnesses are retained. An opaque relation can describe unsupported
operations, nonintegral constants, external holes or conditional branches.
No integer tag is supplied by interval endpoints or inferred for an opaque leaf.

`integer e` recognizes guaranteed integer values. `infer d e` either returns a
residue or `none` for a **caller-selected modulus**. It does not search for an
optimal modulus or use gcd normalization. Constants retain their exact residue;
floor is recognized modulo 1. Add/subtract propagate two successful residues.
Scaling checks divisibility of its coefficient and the child's integer provenance;
otherwise it scales a recursively inferred residue. Unsupported cases fall back.
Even multiplying an opaque child by zero does not fabricate integer provenance.

`integer_sound` and `infer_sound` are conditional on an actual `Value R e p z`.
Recognizing floor says its defined values are integers; it does not say its
operand is defined. A successful tag may coexist with an empty domain. All
operand evaluation remains strict, including scaling by zero.

`exclude` uses the merged positive-modulus closed-window theorem. The optional
`exclude_enclosure` bridge intersects an existing sound partial enclosure with
the target window, retaining the very same semantic value and parameter.
Inference failure, or failure of the strict ceiling/floor gap, supplies no
exclusion. Neither theorem concludes existence from an unresolved case.

## Controls and scope

[Fixtures](tests/ResidueInference.lean) cover inferred stride and alignment,
negative affine arithmetic, unsupported real terms, external holes and branches.
`2*floor(x)` receives even provenance; `floor(2*x)` does not and is proved to
attain 1 at x=1/2. A floor tag from one term cannot leak to another real term.
The original real-input falsifier still attains 1. An opaque branch integral at
one parameter and nonintegral at another remains untagged. Finally,
`0*floor(1/x)` at zero has no semantic value despite a successful conditional tag.

This is a derived proof-side inference mechanism, not a new claim about Tupper's
algorithms. The existing [floor/ceiling source correspondence](MONOTONE_INTEGER_BOUNDS.md)
and [thesis concordance](THESIS_CONCORDANCE.md) describe the relevant floor and
discrete-image context. No source claim is made that this particular inference
pass occurs in Tupper. No floating-point assumption changes.

Application efficacy is not established by the stride example or the public
controls below. No existing application prover or renderer was measured, and no
integration is justified by this limited evidence. Private corpus material and
private-study aggregates are excluded from this document.

Run `lake build ResidueInference`, `lake env lean tests/ResidueInference.lean`
and `./check.sh`. Library and fixture audits use the existing allowlist. Independent semantic review covers the proof and study scope.
This module is independent of split-division work.

## Matched public efficacy controls (not a renderer benchmark)

The source-grounded public fallback is Tupper's SIGGRAPH 2001 Fig. 10(c),
`y=floor(x)` on `[-4,7]^2` ([paper](https://www.dgp.toronto.edu/papers/jtupper_SIGGRAPH2001.pdf#page=6)).
A separately labeled **derived** control uses `y=2*floor(x)`. Both use the same
44 by 44 closed quarter-unit cells and zero subdivision. The proof-side study
uses exact rational endpoint hulls, the modulo-1 certificate, and the inferred
certificate. No C execution, renderer or application prover is measured.

| Control (1,936 cells each) | Hull exclusions | Integer exclusions | Inferred exclusions |
| --- | ---: | ---: | ---: |
| Public floor control | 1,809 | 1,831 | 1,831 |
| Derived scaled-floor control | 1,848 | 1,870 | 1,881 |

Thus the source control gains 22 exclusions from **integrality**, and none from
nontrivial residues. The derived scaled case gains another 11 from parity after
22 integrality exclusions. Remaining cells are labeled unresolved, not existence;
a separate finite-image oracle finds 105 and 55 attained cases respectively.
All reported exclusions agree with that oracle. These are exact-arithmetic
sanity counts from an independent local Python harness, not kernel-checked counts
or a proof of that harness. Lean proves the inference rules and representative
controls; it does not verify a renderer, parser or the local counting program.

The public floor control shows no nontrivial-modulus gain beyond integrality.
That does not establish absence of application benefit: application efficacy was
not measured. The derived scaled control demonstrates only the stated synthetic
parity effect. No integration is proposed.
