# Vendored Riemann--Roch core

This directory contains the transitive Lean source dependencies of the
coordinate-free Riemann--Roch endpoint from Guanghao Li's
[`vaca22/riemann-roch-function-fields`](https://github.com/vaca22/riemann-roch-function-fields),
upstream commit `dbca5beed1da77e2ecd1eec207d0451fa57e8aa6`.

The source is distributed under Apache License 2.0; the upstream license is
preserved verbatim in [`LICENSE`](LICENSE).  The imported development is a
proof library, not a mathematical assumption: Lean checks every theorem from
its source in this repository.

## Local compatibility port

Upstream targets Lean/Mathlib `v4.31.0`.  BGS currently uses Lean
`v4.32.0-rc1` and its matching Mathlib revision.  The source was verified
against a fresh checkout of the commit above, then the following five modules
received mechanical migrations to Mathlib's current explicit
ramification/inertia-degree API:

- `SeparableRelNorm.lean`
- `Place.lean`
- `PlaceEquiv.lean`
- `FunctionField/Divisor.lean`
- `Genus/Ramification.lean`

The vendored set is the exact import closure of
`RiemannRoch.CoordinateFree.RiemannRoch`; the independent elliptic-curve
application is intentionally not copied.  Run

```text
lake build RiemannRoch.CoordinateFree.RiemannRoch
lake env lean RiemannRoch/AxiomCheck.lean
```

to rebuild the endpoint and audit its proof dependencies.
