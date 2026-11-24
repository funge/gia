# Finite quadratic families

Tupper §2.9.5, [printed p.30 / PDF p.46](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=46),
defines paired bounds `p + qα + rα²` and requires them to be well-defined and
noncollapsing throughout the parameter domain. The original page was visually
checked. It does not give a general extremum algorithm there; later chapters
handle particular demotions. Its extended-coefficient examples are not finite
rational polynomials and are not silently interpreted using totalized infinity
arithmetic here.

[QuadraticFamilies.lean](QuadraticFamilies.lean) implements the finite rational
instance and a **derived** finite cross-term extension, with the existing shared
vector `t : Fin n → Real`. A form consists of the existing affine form plus
`Σᵢ Σⱼ rᵢⱼ tᵢtⱼ`. At n=1, `coefficients_value` and
`one_parameter_representation` give exactly the source's three-coefficient
semantics. The matrix representation for n>1 is not canonical: antisymmetric
cross coefficients can cancel. We claim no unique multivariate coefficient
normal form.

## Exact operations and embedding

- `embed_value` and `embed_injective` embed existing affine forms exactly.
- `product_value` proves that the coefficient-expanded product of two affine
  forms equals the product of their real values at **one shared vector**.
- `add_value`, `sub_value`, `scale_value` prove exact quadratic addition,
  subtraction and rational scaling. Arbitrary quadratic multiplication is not
  provided: the fixture `fourth_power_not_quadratic` proves lack of closure.
- `fromAffine_contains` transports the existing affine interval family exactly.
  Quadratic `Bounds` requires a proof of order throughout the cube; endpoint
  checks are not substituted for that obligation. This is a representation and
  semantic contract, not an automatic quadratic noncollapse solver.

## Sound demotion, distinct from optimization

For finite cube inputs every monomial tᵢtⱼ is in [0,1]. `encloses` uses that fact
and the existing affine enclosure to give coarse constant bounds. It does not
assume the monomials are independently attainable. `demotion_encloses` and
`constant_demotion` connect paired quadratic bounds to the existing family
soundness/demotion interface, keeping the cube and the caller's actual witness.
Existing external-domain restriction remains applicable; no undefined expression
values are created by this total finite-polynomial representation.

For a one-parameter affine product, `product_chord_demotion` reuses
`affine_product_encloses` and the existing chord-curvature correction. It is not
another proof or implementation of that operator. For α(1−α), the corners give
zero but the midpoint gives 1/4. The reused chord bounds give [0,1/4], with both
extrema attained, while the deliberately coarse coefficient demotion gives
[−1,1]. The fixture also shows a pair of quadratic bounds ordered at both ends
but collapsed at the midpoint. Thus corner checking alone is unsound for general
quadratic noncollapse or extrema.

[Tests](tests/QuadraticFamilies.lean) cover these controls, a two-coordinate cross
term, same-vector versus independent-parameter products, cancellation, and the
projection client. All definitions are proof-side/noncomputable; no native path,
rounding assumption, arbitrary multivariate optimization or optimality claim is
introduced. Run the existing pinned `./check.sh` and namespace/axiom gate.

## Ledger and review placement

Checked for §2.9.5: finite rational quadratic coefficient semantics, exact affine
embedding and supported operations, paired noncollapse obligation, and sound
demotion with interior-extremum controls. The n>1 cross-term product is a derived
extension linked to §2.9.6, not text attributed to §2.9.5. Still open: full
real/extended coefficients and exceptional bound validity, general nonlinear
operator demotion and a general optimizer. These results stay in review unit 3;
no new branch or public change is needed. Earlier source-interpretation
qualifications are unchanged.
