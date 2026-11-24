# General family demotion with partial domains

[GeneralFamilyDemotion](GeneralFamilyDemotion.lean) proves representation-independent
composition for real-valued families. Source, intermediate and target representation
carriers can be arbitrary types; their supplied interpretations are sets of real
values at a parameter plus the existing `DomainBounds` classification. There is
no new numeric runtime, family syntax, exception carrier or FP contract.

## Source and precise scope

Tupper §2.9.3 printed p.29 / PDF p.45 gives same-parameter inclusion and outward
function demotion. §§2.11.1–2 printed pp.34–35 / PDF pp.50–51 add the independent
value and domain obligations and require classification-preserving demotion.
The original [PDF p.50](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=50)
and [PDF p.51](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=51) were visually
checked for this milestone. The p.34 inclusion formula uses a three-valued
equivalence followed by optimistic Boolean projection, not merely the implication
in the damaged Markdown transcription. The existing `DomainBounds.Compatible`
and `UniversalSound` already encode the adopted compatibility interpretation;
the new theorem explicitly agrees with that contract on `PartialEnclosure`.

`Sound V D A R` means, for each parameter p and each admitted input w:

* every actual result of `R p w` belongs to `V p`;
* `D.definite p` implies this input has a result;
* a result for this input implies `D.possible p`.

A tuple of operands can be the single w; no Cartesian independence is imposed.
An arbitrary relation may have several results. This includes partial functions
but does not claim the source defines all relations as functions. Parameters
are arbitrary types; `[0,1]^n` can be supplied as a subtype or admission guard.
Sentinel undefinedness is represented by absence of a real result, not by IEEE
NaN or the exceptional-comparison layer.

## General theorem and premises

`Demotes V D U E` requires:

1. Existing `DomainConstraints.Refines D E`: target definite implies source
   definite, and source possible implies target possible.
2. At every source-possible parameter, `V p ⊆ U p`.

Numeric payloads at source-impossible parameters need not be related: soundness
already rules out any actual result there. This matches the source allowance
for arbitrary numeric bounds on undefined domains. It does **not** permit
ignoring a partially defined fiber, since that fiber is possible.

`sound_demote : Sound V D A R → Demotes V D U E → Sound U E A R`
proves both value enclosure and per-input domain compatibility. `model_demotion`
lifts it to a model followed by a demoter between arbitrary representation types.
Reflexivity and transitivity support multiple stages. Classification weakening
reuses the earlier leaf theorem, rather than identifying numeric inclusion with
domain preservation.

`exact_sound` uses actual output sets and the existing `exactInputDomain`.
`exact_hull_sound` projects them through the existing extended least closed hull
while retaining that exact domain envelope. The nonempty-input guard is an
explicit project convention: empty input fibers have neither definite nor
possible classification. This does not claim a source Boolean infimum convention
for an empty input family. In particular, a nonempty numeric hull is not evidence
that every admitted input is defined.

`affine_to_constant` instantiates this same Demotes relation with existing
`LinearInterval.hull`; `affine_constant_sound` is exactly a use of the general
soundness theorem. The `[0,1]` possible-domain guard is essential. The previous
[finite bridge](FAMILY_DEMOTION.md) supplies leastness of the closed projection;
we do not reprove it. `restrict_sound` retains external holes in both the actual
relation and domain classification.

## Checked limitations and examples

[Fixtures](tests/GeneralFamilyDemotion.lean) prove the seed `x=t` sound through
the actual affine-to-constant instance. Shared-parameter subtraction yields only
0; projecting both inputs to `[0,1]` before independent subtraction admits 1.
The wider result is sound but loses correlation; membership is not attainment.

The projected model retains a hole at `t=1/2`. A separate Bool-input relation
has a value at `true` but none at `false`: its exact domain is possible but not
definite. Replacing that classification by totality fails even if numeric bounds
are all of ℝ. Empty-input controls and arbitrary payload demotion on nowhere-defined
fibers check the other boundaries.

This is a general semantic inclusion theorem, **conditional on proved
interpretations and demotion obligations**. It does not construct arbitrary
function approximations, guarantee representation availability, prove optimal
demotion, or establish numerical classification preservation for arbitrary
source descriptor functions. Extended exceptional arithmetic, all surveyed family
instances, full Chapter 2 completion and native implementation refinement remain
open. No new FP assumption is used.

## Validation and integration

```sh
lake build GeneralFamilyDemotion
lake env lean tests/GeneralFamilyDemotion.lean
RELGRAPH_CHECKOUT=/path/to/pinned/relgraph ./check.sh
```

See [validation](VALIDATION.md), [completion ledger](CHAPTER2_COMPLETION.md) and [concordance](THESIS_CONCORDANCE.md).
Later property tracking and tagged conversion remain separate review units.
