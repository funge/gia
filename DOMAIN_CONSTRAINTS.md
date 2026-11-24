# Same-parameter domain constraints (§2.11.4)

Source: Tupper, *Graphing Equations with Generalized Interval Arithmetic* (1996),
§2.11.4, printed pp.35–36 / [PDF pp.51–52](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=51).
The local transcription was read first and both original PDF pages visually
checked. The source conjoins every constraint at the same parameter α. A total
operation collects its operands' constraints; a partial operation also introduces
an operation-domain constraint. Classification-preserving demotion is required.

## What this tranche proves

`DomainConstraints.lean` reuses `DomainBounds.inter`, `Compatible`,
`PartialEnclosure.UniversalSound` and the existing affine reciprocal-sum theorem.
It depends on the Boolean composition milestone (#32), without changing that PR.

* `allDomains` folds a finite list using existing intersection. The empty family
  imposes True; `all_definite` and `all_possible` characterize the result by
  conjunction at one parameter. `all_description_ext` shows order/repetition
  cannot change classification when list membership agrees.
* `description` interprets a consistent definite/possible pair as the existing
  F/TF/T type. `description_compatible` proves Boolean membership is precisely
  the existing two-way definedness compatibility condition. TF here permits
  either Boolean; it does not assert that both are attained.
* `description_inter` and `all_description` connect domain conjunction to the
  proved Boolean tables. `all_compatible` retains one parameter for all constraints.
  `partial_guard_compatible` additionally conjoins a supplied operation guard.
* `Refines D E` means E may weaken definite membership and enlarge possible
  membership, pointwise. `refines_description` proves information inclusion;
  `all_refines` lifts componentwise weakening through a common finite family.
  `weaken_compatible` and `weaken_universal` preserve actual semantic soundness.
* `constraints_universal` connects the family to existing partial-enclosure
  semantics at the SAME represented input witness. Its premises require actual
  value enclosure and an independently proved equivalence between operation
  definedness and the constraints. It does not assume that possible constraints
  imply existence or that separately represented inputs may be combined.
* `reciprocal_constraints` instantiates the domain bridge with the existing
  `affine_sum_defined_iff`: a finite reciprocal sum is defined exactly when all
  denominators are nonzero at the same environment. No finite range near a pole
  is inferred, and the expression/evaluator implementation is unchanged.

## Boundary of the correspondence

This is a general parameter-type, finite-constraint **predicate interpretation**
of the source conjunction and classification-preservation obligations. It is not
an implementation of the full numeric description language `f_i(d_i(α))`, an
algorithm producing domain-demotion families, or a new abstract-domain solver.
`description` uses classical decisions and is a semantic proof interface, not a
native executable classifier. Existing decidable domain queries remain unchanged.

The sufficient componentwise `all_refines` rule is not the only valid demotion:
a differently shaped output family may be justified by a proof of `Refines`
between its aggregate bounds. No numerical rounding rule is assumed to imply
that condition automatically. New FP assumptions are neither needed nor added.
The source's full number-system encoding, extended endpoints and λ conventions,
optimal domain extension, and §2.12 recursive property system remain open.

For a total operation, reuse of the collected constraints needs its actual
operation-definedness equivalence. For a partial operation, the extra guard must
be proved sound at the same input; `partial_guard_compatible` does not infer it.
The caller-supplied equivalence in `constraints_universal` states that obligation
explicitly. Existing affine reciprocal semantics supplies one concrete instance.

## Controls and verification

[Fixtures](tests/DomainConstraints.lean) check separately satisfiable but jointly
inconsistent constraints, closed shared boundaries, a punctured domain, weakening,
unknown compatible with False, empty constraints, a genuine reciprocal pole,
operation-guard composition, order/duplicate invariance and the universal bridge.
An empty represented-input fiber demonstrates why `universal_projects` still
needs its nonempty-input premise: universal soundness can be vacuous even when
the empty conjunction describes a definite parameter.

```sh
lake build DomainConstraints
lake env lean tests/DomainConstraints.lean
./check.sh
```

No new native implementation, production default, floating-point contract,
performance claim or renderer integration. See [Chapter 2 completion criteria](CHAPTER2_COMPLETION.md),
[coverage checklist](CHAPTER2_CHECKLIST.md), [concordance](THESIS_CONCORDANCE.md)
and [validation](VALIDATION.md). The Boolean prerequisite is under review;
this follow-on is kept local until qualified and coordinated.
