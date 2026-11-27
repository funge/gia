# One-hidden-layer ReLU inference

This milestone encloses a fixed network with `n` input features, `h` hidden ReLU
neurons, and one scalar affine output:

`aⱼ(x) = max(0, Σᵢ Wⱼᵢ xᵢ + bⱼ)`

`prediction(x) = Σⱼ vⱼ aⱼ(x) + c`.

All weights and biases are fixed rationals. Features are real values in finite
nonempty closed rational intervals. Both dimensions are arbitrary finite natural
numbers, including zero. This is inference, not training or a statistical claim.

## Reused proofs and shared inputs

[ReluNetworkInference.lean](ReluNetworkInference.lean) imports the
[linear-model proof](LINEAR_MODEL_INFERENCE.md), without a dependency on the
logistic proof. `relu_monotone` and `relu_sound` justify clipping each affine
neuron's bounds at zero. `hidden_sound` proves the vector of actual activations
belongs to the resulting box. `sound` then applies the existing affine enclosure
proof to the output layer.

Every neuron in `activations` uses the **same input vector**. The final soundness
theorem does not assume hidden activations are independent. It needs only their
individual containments. Independent feature boxes are the input model; further
restrictions on inputs do not invalidate soundness.

`bounds` is an executable exact-rational reference enclosure algorithm. The
prediction itself has real semantics. This slice adds no directed hardware path,
ReLU comparison contract, C/FFI code, or floating-point premise. Input uncertainty
and loss of correlation are separate from roundoff; the latter is not introduced
by this reference algorithm.

## Why output tightness generally fails

The [fixtures](tests/ReluNetworkInference.lean) give both hidden neurons weight 1
and bias 0, on `x ∈ [-1,1]`. Their marginal bounds are each `[0,1]`, and each
neuron attains both endpoints. Output weights `[1,-1]` with zero bias yield:

- layerwise output bounds `[-1,1]`;
- exact network output `ReLU(x) - ReLU(x) = 0` for every input;
- neither output bound is attained;
- the independent hidden box contains `(0,1)`, but no shared input produces it.

Thus the enclosure width is 2 while the actual range has width 0. This is a
checked correlation example, not a runtime measurement or a claim that the
algorithm is unsound. In particular, membership in an output bound is not proof
that the network attains that value.

`extrema_of_joint_reachability` provides a sufficient condition for endpoint
attainment: every vector in the hidden box is produced by some admitted input.
That condition is stronger than necessary and is not asserted for arbitrary
networks. Individual neuron endpoint attainment cannot replace it. The theorem
reuses the affine output's endpoint witnesses rather than assuming the desired
output equality.

## Positive and boundary controls

A second example is `3 * ReLU(2x - 1) + 1` on `[0,1]`. The public `bounds` API
returns `[1,4]`; the fixtures prove all outputs are positive and that inputs 0
and 1 attain those bounds. Other controls cover a negative preactivation interval,
a zero boundary, a crossing-zero interval, and zero hidden neurons (output equals
the bias). The examples are kernel checked and the rational bounds are evaluated
through the same API used by the soundness theorem.

## Verify and scope the next step

```sh
lake build ReluNetworkInference
lake env lean tests/ReluNetworkInference.lean
./check.sh
```

This is a small composition proof, not an architecture framework. A later step
could preserve selected activation relations to improve precision, or connect a
separately justified directed backend. Neither is required by this theorem;
native inference, training, and general network-range optimization remain outside
this milestone.
