import GenMarkoff.Symmetric.FiberDynamics
import BGS.Markoff.Core.FiniteRotationEigenvalues

/-!
# Reusing the BGS `SL₂` rotation kernel

The symmetry-enabled affine half-step has the same linear matrix as the
generic BGS normalized rotation.  These identities are the explicit theorem
boundary at which the symmetric development reuses the pinned BGS linear
algebra and torsion-eigenvalue results.
-/

namespace GenMarkoff.Symmetric.Opening

universe u

open scoped Matrix

theorem fiberMatrix_eq_bgsRho
    {R : Type u} [CommRing R] (t : R) :
    fiberMatrix t = BGS.Markoff.rho t :=
  rfl

theorem fiberMatrixSL_eq_bgsRhoSL
    {R : Type u} [CommRing R] (t : R) :
    fiberMatrixSL t = BGS.Markoff.rhoSL t :=
  rfl

theorem halfStepOrder_eq_bgsRotationOrder
    {R : Type u} [CommRing R] (t : R) :
    halfStepOrder t = BGS.Markoff.rotationOrder t :=
  rfl

/-- The order of the old two-Vieta rotation is the order of the square of the
BGS matrix, whereas the selected one-step order is its unsquared order. -/
theorem squaredRotationOrder_eq_bgsRotationOrder_div_gcd
    {R : Type u} [CommRing R] (t : R) :
    squaredRotationOrder t =
      BGS.Markoff.rotationOrder t /
        Nat.gcd (BGS.Markoff.rotationOrder t) 2 := by
  simpa only [halfStepOrder_eq_bgsRotationOrder] using
    squaredRotationOrder_eq_halfStepOrder_div_gcd t

/-- Reused BGS eigenvalue parametrization for a symmetric fiber trace. -/
theorem exists_torsionEigenvalue_of_finiteOrder_fiberMatrix
    {K : Type u} [Field K] [IsAlgClosed K] (t : K)
    (hfinite : IsOfFinOrder (fiberMatrixSL t)) :
    ∃ w : Kˣ, IsOfFinOrder w ∧ t = BGS.Markoff.splitTorusTrace w := by
  rw [fiberMatrixSL_eq_bgsRhoSL] at hfinite
  exact BGS.Markoff.finiteOrderRotation_has_torsion_eigenvalue t hfinite

end GenMarkoff.Symmetric.Opening
