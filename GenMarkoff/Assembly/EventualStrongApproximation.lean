import GenMarkoff.Arithmetic.EventualAdmissibility
import GenMarkoff.Assembly.DivisibleOrbitTransitivity
import GenMarkoff.Assembly.RotationDivisibility

/-!
# Eventual strong approximation from the giant-orbit input

This file connects the internally proved generic generalized Martin
divisibility theorem to the rotation graph and then performs the final BGS
giant-orbit assembly.  This conditional assembly takes one mathematical
input explicitly:

* `GeneralizedGiantOrbitStatement`, viewed here as the output of the direct
  coefficient-dependent opening, middle-game, endgame, and cage route.

The production general theorem later proves this proposition downstream from
rotation transitivity by the connecting-fiber route.
-/

namespace GenMarkoff

/-- Integral nondegeneracy gives eventual divisibility for the rotation
orbits used by the local graph. -/
theorem IntegrallyNondegenerate.eventually_rotationOrbitDivisibility
    {a : Coefficients ℤ} (ha : IntegrallyNondegenerate a) :
    EventuallyRotationOrbitDivisibility a := by
  obtain ⟨vietaThreshold, hVieta⟩ :=
    ha.eventually_vietaOrbitDivisibility
  refine ⟨max vietaThreshold 5, ?_⟩
  intro p hp hpLarge
  have hpVieta : vietaThreshold ≤ p :=
    (Nat.le_max_left _ _).trans hpLarge
  have hpFive : 5 ≤ p :=
    (Nat.le_max_right _ _).trans hpLarge
  exact rotationOrbitDivisibility_of_vietaOrbitDivisibility
    p hp hpFive (modCoefficients a p) (hVieta p hp hpVieta)

/-- The formalized endpoint of the generalized BGS strategy after the generic
divisibility argument.

Once the generalized giant-orbit statement is proved, no further mathematical
assumption is required to obtain the project's eventual strong-approximation
target. -/
theorem eventualStrongApproximationStatement_of_giantOrbit
    (hgiant : GeneralizedGiantOrbitStatement) :
    EventualStrongApproximationStatement :=
  eventualStrongApproximationStatement_of_giantOrbit_and_orbitDivisibility
    hgiant fun _a ha => ha.eventually_rotationOrbitDivisibility

/-- Compatibility wrapper for the former conditional endpoint.  The broad
exceptional-case Martin specification is no longer needed for the eventual
integrally nondegenerate theorem, because all sufficiently large reductions
lie in the proved generic branch. -/
theorem eventualStrongApproximationStatement_of_generalizedMartin_and_giantOrbit
    (_hMartin : GeneralizedMartinDivisibilityStatement)
    (hgiant : GeneralizedGiantOrbitStatement) :
    EventualStrongApproximationStatement :=
  eventualStrongApproximationStatement_of_giantOrbit hgiant

end GenMarkoff
