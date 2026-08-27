# Generalized Markoff strong approximation

This repository formalizes a strong-approximation theorem for a
three-parameter family of affine cubic surfaces.

## Main theorem

For integers `a₁`, `a₂`, and `a₃`, let `Xₐ` be the affine cubic surface over
the integers defined by

```text
x₁² + x₂² + x₃²
  + a₁*x₂*x₃ + a₂*x₃*x₁ + a₃*x₁*x₂
  = (3 + a₁ + a₂ + a₃)*x₁*x₂*x₃.
```

Assume

```text
3 + a₁ + a₂ + a₃ ≠ 0,
a₁² ≠ 4,  a₂² ≠ 4,  a₃² ≠ 4.
```

> **Theorem.** There exists a bound `p₀ = p₀(a₁, a₂, a₃)` such that, for
> every prime `p ≥ p₀`, the coordinatewise reduction map
> `Xₐ(ℤ) → Xₐ(𝔽ₚ)` is surjective.

Here the coefficients in the equation for `Xₐ(𝔽ₚ)` are reduced modulo `p`.
Equivalently, every solution of the equation modulo a sufficiently large prime
is the reduction of an integral solution of the same equation.

## What Challenge.lean asks

[Challenge.lean](Challenge.lean) defines the integral solution set, the
solution set modulo `p`, and the coordinatewise reduction map between them. Its
theorem `generalizedMarkoff_reduction_surjective_of_large_prime` asks Lean to
prove exactly the theorem above for every coefficient triple satisfying the
displayed hypotheses.

[Solution.lean](Solution.lean) supplies an explicit value
`explicitCutoff a₁ a₂ a₃` for `p₀` and proves the required surjectivity for
every prime beyond that bound.

## Repository map

- [Challenge.lean](Challenge.lean) is the elementary statement built directly
  on Mathlib and existentially quantifies the numerical cutoff.
- [Solution.lean](Solution.lean) defines the explicit cutoff, supplies it as
  the existential witness, and imports the proved production endpoint.
- [comparator.json](comparator.json) selects the theorem and permitted axioms.
- [GenMarkoff/](GenMarkoff/) contains the production proof development.
- [GenMarkoff.lean](GenMarkoff.lean) is the production library root.
- [BGS/](BGS/) and [RiemannRoch/](RiemannRoch/) contain the transitive proof
  dependencies vendored from the pinned markoff-modp revision.
- [scripts/AxiomAudit.lean](scripts/AxiomAudit.lean) records declaration-level
  axiom expectations.
- [formalization.yaml](formalization.yaml) records scope, provenance,
  automation, fidelity, and review metadata.
- [docbuild/](docbuild/) is the nested doc-gen4 project.

## Reproducible environment

- Lean: `leanprover/lean4:v4.32.0`
- Mathlib: resolved and pinned in `lake-manifest.json`
- Vendored BGS/markoff-modp source revision:
  `ac8e9ec37a3d56dddb55870d379f53e5526dc0c7`

All proof dependencies are contained in the repository at pinned public
revisions.

## Verification

From the repository root:

```text
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
ruby scripts/validate-formalization.rb
```

Build API documentation with:

```text
cd docbuild
lake build GenMarkoff:docs
```

On Linux with Git, Go, Ruby, Rust/Cargo, Python 3, and Landrun available, run
the complete independent comparison and NanoDa replay:

```text
./scripts/verify-comparator.sh
```

The deliberate `sorry` in `Challenge.lean` marks the theorem selected for
comparison. The production `GenMarkoff/` library and `Solution.lean` supply its
complete proof.

## Mathematical sources

The principal sources and the exact relationship of each to the formalization
are recorded in [formalization.yaml](formalization.yaml). The direct literature
list contains these two items:

- Nathaniel Kingsbury-Neuschotz,
  [*Strong Approximation for the Relative Character Variety of the Four-Times Punctured Sphere*](https://arxiv.org/abs/2603.04096v3),
  especially Theorem 4.3;
- Matthew de Courcy-Ireland, Matthew Litman, and Yuma Mizuno,
  [*Divisibility by p for Markoff-like Surfaces*](https://arxiv.org/abs/2509.02187v3),
  especially the generic branch of Theorem 1.1.

The vendored dependencies and their further mathematical sources are recorded
by the related [markoff-modp project](https://github.com/yuma-mizuno/markoff-modp).

## Licence and submission

This repository snapshot is licensed under Apache-2.0. Cited sources and Git
dependencies retain their own licences.

A final public commit can be submitted through the
[Palomar submission form](https://submit.palomar-registry.org/) using its full
40-character commit SHA.
