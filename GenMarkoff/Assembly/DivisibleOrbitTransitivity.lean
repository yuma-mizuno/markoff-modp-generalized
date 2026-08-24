import GenMarkoff.Assembly.FiniteOrbit
import GenMarkoff.Core.Statements

/-!
# From a giant divisible rotation orbit to transitivity

This is the coefficient-independent final assembly step in the generalized
BGS strategy.  It does not assume or assert the still-open generalized
giant-orbit theorem.
-/

namespace GenMarkoff

/-- If one rotation orbit has complement smaller than `p` and every rotation
orbit cardinality is divisible by `p`, then the rotation action is transitive. -/
theorem rotationStrongApproximationAt_of_small_complement_and_orbitCard_dvd
    (a : Coefficients ℤ) (p : ℕ) (hp : p.Prime)
    (x : PuncturedSolutionSurface (modCoefficients a p))
    (hsmall : rotationOrbitComplementCard x < p)
    (hdiv : RotationOrbitDivisibilityAt a p hp) :
    RotationStrongApproximationAt a p hp := by
  letI : Fact p.Prime := ⟨hp⟩
  exact FiniteOrbit.transitive_of_complementCard_lt_and_orbitCard_dvd
    p x hsmall hdiv

/-- A `p ^ epsilon` complement bound with `epsilon < 1` is strictly smaller
than `p`. -/
theorem exists_rotationOrbitComplementCard_lt_prime_of_hasGiantRotationOrbitAt
    (a : Coefficients ℤ) (p : ℕ) (hp : p.Prime)
    (epsilon : ℝ) (hepsilon : epsilon < 1)
    (hgiant : HasGiantRotationOrbitAt a p hp epsilon) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ x : PuncturedSolutionSurface (modCoefficients a p),
      rotationOrbitComplementCard x < p := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := hgiant
  refine ⟨x, ?_⟩
  have hpReal : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hrpow : (p : ℝ) ^ epsilon < (p : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hpReal hepsilon
  have hreal : (rotationOrbitComplementCard x : ℝ) < (p : ℝ) :=
    hx.trans_lt hrpow
  exact_mod_cast hreal

/-- The short BGS assembly at one prime, for the generalized rotation action. -/
theorem rotationStrongApproximationAt_of_hasGiantRotationOrbitAt_and_orbitDivisibility
    (a : Coefficients ℤ) (p : ℕ) (hp : p.Prime)
    (epsilon : ℝ) (hepsilon : epsilon < 1)
    (hgiant : HasGiantRotationOrbitAt a p hp epsilon)
    (hdiv : RotationOrbitDivisibilityAt a p hp) :
    RotationStrongApproximationAt a p hp := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ :=
    exists_rotationOrbitComplementCard_lt_prime_of_hasGiantRotationOrbitAt
      a p hp epsilon hepsilon hgiant
  exact rotationStrongApproximationAt_of_small_complement_and_orbitCard_dvd
    a p hp x hx hdiv

/-- Eventual giant-orbit control with one exponent below one, together with
eventual rotation-orbit divisibility, implies eventual strong approximation. -/
theorem eventuallyRotationStrongApproximation_of_giantOrbit_and_orbitDivisibility
    (a : Coefficients ℤ) (epsilon : ℝ) (hepsilon : epsilon < 1)
    (hgiant : ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p →
      HasGiantRotationOrbitAt a p hp epsilon)
    (hdiv : EventuallyRotationOrbitDivisibility a) :
    EventuallyRotationStrongApproximation a := by
  obtain ⟨giantThreshold, hgiant⟩ := hgiant
  obtain ⟨divisibilityThreshold, hdiv⟩ := hdiv
  refine ⟨max giantThreshold divisibilityThreshold, ?_⟩
  intro p hp hpLarge
  have hpGiant : giantThreshold ≤ p :=
    (Nat.le_max_left _ _).trans hpLarge
  have hpDivisibility : divisibilityThreshold ≤ p :=
    (Nat.le_max_right _ _).trans hpLarge
  exact rotationStrongApproximationAt_of_hasGiantRotationOrbitAt_and_orbitDivisibility
    a p hp epsilon hepsilon (hgiant p hp hpGiant) (hdiv p hp hpDivisibility)

/-- The formalized final assembly: the generalized giant-orbit statement and
eventual rotation-orbit divisibility imply the project's eventual strong-
approximation target. -/
theorem eventualStrongApproximationStatement_of_giantOrbit_and_orbitDivisibility
    (hgiant : GeneralizedGiantOrbitStatement)
    (hdiv : ∀ a : Coefficients ℤ,
      IntegrallyNondegenerate a → EventuallyRotationOrbitDivisibility a) :
    EventualStrongApproximationStatement := by
  intro a ha
  exact eventuallyRotationStrongApproximation_of_giantOrbit_and_orbitDivisibility
    a (1 / 2 : ℝ) (by norm_num)
      ((hgiant a ha) (1 / 2 : ℝ) (by norm_num)) (hdiv a ha)

end GenMarkoff
