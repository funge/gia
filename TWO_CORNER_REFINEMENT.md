# Observed-outcome refinement for two-corner division

[TwoCornerRefinement.lean](TwoCornerRefinement.lean) is a local proof-only follow-on
to [two-corner extrema](TWO_CORNER_DIVISION.md). It does not change an executor,
rounding, backend, renderer, or batching. It is independent of the square branch.

## What is proved

`Refines decode new old` records finite decoded endpoints and the inequalities
`old.lower ≤ new.lower` and `new.upper ≤ old.upper`. `Refines.contains` turns
that into pointwise real-set inclusion. It does not assert raw equality or, on
its own, that the new interval encloses the intended operation.

`same_observations_refine` proves the structural assembly comparison. If the
four-corner assembly succeeds, and the new lower and upper paired observations
are selected from those same four results, the two-pair assembly succeeds and
refines the old result. The hypotheses are the existing `SelectSound` contracts
for min/max and `ResultSound` for the four observations. This proof actually
compares the nested min/max assembly with the chosen endpoints; the two results
are not defined to be equal. Any choice of pairs satisfies this structural
inclusion, but correct corner selection is still needed for operation enclosure.

`observations` associates each operand pair with its observed paired result.
`guarded_refinement` connects the structural theorem to division. Its hypotheses
explicitly require:

- all four input endpoints decode to reals and both intervals are ordered;
- `CompareSound`, the decoded zero, and the existing strict nonzero guard;
- the existing `TwoCornerDivision.select` chooses the supplied real corner pairs;
- the chosen operands decode to those corners, and their outcome associations
  occur among the old four calls;
- the four existing division `CallSound` contracts and min/max `SelectSound`;
- success of the old guarded assembly.

The conclusion supplies a successful new assembly, decoded containment in the
old result, and enclosure of every quotient of actual input witnesses with a
nonzero denominator. No exact rounding, completeness, or new FP assumption is
introduced. Correct real corner selection remains an explicit hypothesis; no
native selector is implemented here. External restrictions can remove actual
input pairs; none of these theorems manufactures missing witnesses.

## Direction-specific agreement, without raw equality

The used directions are explicit: the lower result uses the **first/Down** side
of its paired observation; the upper uses the **second/Up** side. `downValue` and
`upValue` project and decode just those sides. `directional_observations_refine`
weakens whole-pair identity to equality of the decoded used observations. Unused
pair sides and raw tags may differ. `direction_transfer` also transfers any
already-proved enclosure of the selected intermediate bounds, so it composes
with `guarded_refinement` without another arithmetic soundness assumption.

This conditional agreement has a precise availability obligation: if the old
used observation decodes successfully, the equal new projection must also decode
successfully, which entails that the new paired result exists. It does **not**
predict that an independently run backend will supply such an outcome. In
particular, it cannot infer agreement from two separate `CallSound` hypotheses,
or bypass a real paired-call failure caused by an unused direction or environment.
The directional algebra certifies only the new used endpoints; it does not
certify the unused sides of new pairs or establish their full `CallSound`
contract. A production paired backend must still obey its existing contract
and failure rules.
No statement about fenv, exception flags, instruction counts, or raw-bit parity
is proved. These remain distinct from the all-request preservation theorem in
[directed scheduling](DIRECTED_SCHEDULING.md).

## Controls and boundaries

[The fixture](tests/TwoCornerRefinement.lean) checks guarded positive division,
a sound loose omitted observation, success with differing unused pair sides,
selected failure, and the asymmetry where a skipped call fails. A direction
counterexample shows why an upper bound cannot replace the selected Down value
while retaining an enclosure claim.

The invalid-endpoint control uses `Option ℝ` with an undecodable upper endpoint
as a nonfinite/infinity token. Naive selection of only the finite denominator
endpoint can assemble finite output, and those selected calls satisfy their
scalar contracts, but the required finite decoding of the unused input endpoint
is impossible. This is an abstract invalidity model, not native infinity bits or
a claim that extended-real division itself is unsound. It illustrates why input
validation cannot be replaced by the success of selected scalar calls.

The zero-tie control has two distinct Boolean tags both decoding to real zero.
Left- and right-biased tie selectors satisfy the real selection contract but can
choose different tags. Old/new assemblies can therefore have unequal raw tags
and equal decoded bounds. This represents the signed-zero distinction at the
abstract assembly level; it neither tests nor proves actual binary64 zero signs.

The mathematical source remains the derived two-corner rule and the existing
Tupper correspondence recorded in [hardware division](HARDWARE_DIVISION.md).
This is an algebraic assembly refinement, not an additional theorem attributed
to the thesis or a verification of the linked C implementation.

Run `lake build TwoCornerRefinement`, `lake env lean tests/TwoCornerRefinement.lean`,
and `./check.sh` with the pinned toolchain. See [qualification](VALIDATION.md).
This follow-on remains local; it is not part of the two candidate PR heads.
