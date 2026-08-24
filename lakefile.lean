import Lake

open Lake DSL

-- The reusable BGS and Riemann--Roch production sources are vendored from
-- markoff-modp commit ac8e9ec37a3d56dddb55870d379f53e5526dc0c7.
-- Its Blueprint modules and Verso dependency are intentionally absent.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"

package GenMarkoff where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

lean_lib RiemannRoch where
  globs := #[`RiemannRoch.+]

lean_lib BGS where

@[default_target]
lean_lib GenMarkoff where

-- Comparator and lean4export consume legacy `.olean` declarations. The
-- deliberate Challenge placeholder is isolated from the production library.
@[default_target]
lean_lib Challenge where
  roots := #[`Challenge]
  leanOptions := #[⟨`experimental.module, false⟩]

@[default_target]
lean_lib Solution where
  roots := #[`Solution]
  leanOptions := #[⟨`experimental.module, false⟩]
