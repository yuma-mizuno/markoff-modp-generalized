import GenMarkoff.Symmetric.Basic

/-!
# Restricted theorem statements for equal coefficients
-/

namespace GenMarkoff.Symmetric

/-- The giant-orbit half of the BGS strategy, restricted to `(c,c,c)`. -/
def GiantOrbitStatement : Prop :=
  ∀ c : ℤ, 3 * (1 + c) ≠ 0 → c ^ 2 ≠ 4 →
    EventuallyHasGiantRotationOrbit (coefficients c)

end GenMarkoff.Symmetric
