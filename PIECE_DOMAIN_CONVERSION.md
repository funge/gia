# Constructive value/domain conversion for finite bands

Tupper §2.11.1–2 separates value inclusion from domain-classification obligations (printed p.34 / [PDF p.50](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=50)). §2.11.2–4 then requires domain demotion to preserve classifications, describes numeric predicates, and permits conjunctions at the same parameter (printed p.35 / [PDF p.51](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=51), visually checked). This milestone constructs a restricted converter that discharges both obligations. It does not assume an abstract demotion certificate as its conclusion.

## Supported input and construction

[PieceDomainConversion.lean](PieceDomainConversion.lean) uses the existing [mixed endpoint bands](MIXED_ENDPOINTS.md): one real parameter, finite affine endpoints with the existing integer/rational coefficient placements, open/closed flags, and finite rational affine parameter guards. The finite grammar and mixed carrier placement are our explicit model, not a claim that Tupper prescribes this syntax. This is not general semialgebraic quantifier elimination.

For each band `b`, the converter constructs:

- `valueCode b`: its closed numeric endpoint band;
- `domainCode b`: the original guards conjoined with endpoint feasibility;
- `converted b`: their intersection using the existing finite-piece compiler.

Feasibility is `lower < upper` when either endpoint is open, and `lower ≤ upper` otherwise. It is encoded as one additional affine comparison of `lower − upper` with zero, not a supplied proof or oracle. Existing `MixedEndpoints.fiber_nonempty` and `FiniteGuardPieces` semantics establish that this guard holds exactly when the original band has a value. No endpoint order premise is required: reversed and empty open-equal bands remain empty.

`converted_encloses` proves original value inclusion with the same parameter and band witness. `converted_nonempty` proves exact preservation of each band's definedness. `compileValues` and `compileDomain` construct finite codes for a list of bands, with `values_enclose`, `values_nonempty`, and `domain_exact` relating them to the original union. The domain code ignores its output coordinate; it describes parameter membership.

## Classification, including mixed choices

A list also has a per-choice interpretation: the original band is the input witness, and a choice is defined when that band's fiber is nonempty. Using the existing `exactInputDomain`:

- definite means a nonempty list and **every** admitted band has a value;
- possible means **some** admitted band has a value;
- the empty list is neither definite nor possible, following the existing project convention.

`classification_exact` proves equality of both source/target predicates for every real parameter. `coupled_sound` proves value enclosure and `DomainBounds.Compatible` for every original band witness together. This is stronger than preserving only nonemptiness of the union. It is not an assertion that a nondeterministic relation has a unique value or that every enclosed value is attained.

`active?`, `possible?`, `definite?`, and `classify` are executable exact-rational reference checks at rational parameters. Their correctness is proved against the real semantics and the existing F/TF/T `DomainConstraints.description`. The real theorems hold for every real parameter, hence also on the source unit interval. General real-parameter results are mathematical; no arbitrary real comparison implementation is assumed. The checks are not hardware interval arithmetic or a new native hot path.

## Controls and limits

[Kernel fixtures](tests/PieceDomainConversion.lean) cover closed/open singletons, sloping endpoints at equality and reversal, rational interior points, empty/all/mixed classifications, and a two-piece parameter hole. In the hole example both numerical endpoint bands are `[1,1]`, but their guards are `t<0` and `t>0`; retaining only the numerical value admits 1 at zero. The constructed domain code and converted values both reject zero. On either side, one branch is defined and the other is not, so per-choice classification remains TF, not T.

An open upper endpoint can be added by numerical closure when the original band is nonempty. This demonstrates why we claim enclosure, not exact numerical denotation. The feasibility guard prevents closure from inventing a value for an originally empty open singleton. All these controls exercise the constructed finite code, not only separate inequalities. A nine-case `#eval` reference check also executes the same pure rational functions; the kernel fixtures independently prove those outcomes.

This closes a first constructive finite value/domain conversion, including classification preservation. It does not convert arbitrary descriptors, infer the domain of arbitrary nonlinear expressions, minimize piece count, support literal infinite/λ coefficients, or settle unspecified exceptional operations. It introduces no new axioms or FP premises and changes no native/default paths. The [closeout matrix](CHAPTER2_CLOSEOUT.md) separates remaining proof tasks from source problems; Chapter 2 remains incomplete.

Validation is recorded in [VALIDATION.md](VALIDATION.md).
