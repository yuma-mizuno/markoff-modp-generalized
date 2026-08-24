import GenMarkoff.Assembly.EventualStrongApproximation
import GenMarkoff.Symmetric.Statements

/-!
# Final assembly for the equal-coefficient family

The only premise of this module is the restricted giant-orbit theorem.  Orbit
divisibility and the complement argument are the already-proved generalized
ones.
-/

namespace GenMarkoff.Symmetric

/-- The restricted giant-orbit theorem implies restricted eventual strong
approximation without any further geometric assumption. -/
theorem eventualStrongApproximationStatement_of_giantOrbit
    (hgiant : GiantOrbitStatement) :
    EventualStrongApproximationStatement := by
  intro c hs hc
  have ha : IntegrallyNondegenerate (coefficients c) :=
    (integrallyNondegenerate_coefficients_iff c).2 ⟨hs, hc⟩
  exact eventuallyRotationStrongApproximation_of_giantOrbit_and_orbitDivisibility
    (coefficients c) (1 / 2 : ℝ) (by norm_num)
      ((hgiant c hs hc) (1 / 2 : ℝ) (by norm_num))
      ha.eventually_rotationOrbitDivisibility

end GenMarkoff.Symmetric
