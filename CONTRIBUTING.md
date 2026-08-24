# Contributing

Contributions should preserve the audited Palomar boundary and the mathematical
scope recorded in `formalization.yaml`.

1. Keep `Challenge.lean` short, Mathlib-only, and statement-focused.
2. Put proof changes in `GenMarkoff/` and expose the proved endpoint through
   `Solution.lean`.
3. Do not add `sorry`, `admit`, custom axioms, Blueprint dependencies, or
   local path dependencies to the production submission.
4. Keep the ordered coefficient triple fixed and explicit. Coordinate
   permutations must carry the coefficient permutation with them.
5. Keep the individual Vieta group distinct from the two-factor rotation
   group, and use punctured to mean removal of `(0, 0, 0)` only.
6. Update `formalization.yaml`, `README.md`, and `comparator.json` whenever a
   public statement or proof boundary changes.

Before committing, run:

```text
lake build
lake env lean scripts/AxiomAudit.lean
ruby scripts/validate-formalization.rb
git diff --check
```

On Linux, also run `./scripts/verify-comparator.sh`. Stage only the intended
paths and commit the resulting verified milestone locally.
