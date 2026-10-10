import GenMarkoff.General.Cage.OrbitConnecting.ThreeRootEstimate
import GenMarkoff.General.Cage.Connecting.Fiber

/-!
# Reconstructing a square-coset parameter

An orbit-connecting three-root witness records square roots of both component
radicands `alpha * (U ± 2 * k)`.  Their product, divided by `alpha`, is a
square root of the orbit discriminant.  At least one component root is
nonzero, so `orbitCosetBiquadraticToWeightedOrbitQuartic` produces a unit `s`
with `weightedSplitTorusTrace alpha beta (s ^ 2) + gamma = middle`
(`exists_squareCosetParameter_of_orbitConnectingThreeRootWitness`).

For a good witness, the nonzero third root against a nonsquare scalar makes
the centered norm of the middle trace nonsquare.
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The product of the two component radicands is the square scalar
`alpha²` times the orbit discriminant. -/
theorem orbitComponentRadicand_mul_opposite_eq
    (alpha beta k U : K)
    (hproduct : alpha * beta = k ^ 2) :
    orbitComponentRadicand alpha k U *
        orbitOppositeComponentRadicand alpha k U =
      alpha ^ 2 * weightedOrbitDiscriminant alpha beta U := by
  simp only [orbitComponentRadicand,
    orbitOppositeComponentRadicand, weightedOrbitDiscriminant]
  linear_combination 4 * alpha ^ 2 * hproduct

/-- The two component roots cannot vanish simultaneously when the weight
product is nonzero and the characteristic is not two. -/
theorem OrbitConnectingThreeRootWitness.plus_ne_zero_or_minus_ne_zero
    {alpha beta gamma k omegaInv B C0 : K}
    (h2 : (2 : K) ≠ 0)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hproduct : alpha * beta = k ^ 2)
    (w :
      OrbitConnectingThreeRootWitness
        alpha gamma k omegaInv B C0) :
    w.plusRoot ≠ 0 ∨ w.minusRoot ≠ 0 := by
  have hk : k ≠ 0 := by
    intro hk
    have hproductZero : alpha * beta = 0 := by
      rw [hproduct, hk]
      norm_num
    exact (mul_ne_zero halpha hbeta) hproductZero
  by_contra hnone
  push Not at hnone
  rcases hnone with ⟨hplus, hminus⟩
  have hplusEquation := w.plusEquation
  have hminusEquation := w.minusEquation
  rw [hplus, zero_pow (by omega), orbitComponentRadicand] at hplusEquation
  rw [hminus, zero_pow (by omega),
    orbitOppositeComponentRadicand] at hminusEquation
  have hp : w.middle - gamma + 2 * k = 0 :=
    (mul_eq_zero.mp hplusEquation.symm).resolve_left halpha
  have hm : w.middle - gamma - 2 * k = 0 :=
    (mul_eq_zero.mp hminusEquation.symm).resolve_left halpha
  have hfour : (4 : K) * k = 0 := by
    linear_combination hp - hm
  exact (mul_ne_zero
    (by
      rw [show (4 : K) = 2 * 2 by norm_num]
      exact mul_ne_zero h2 h2)
    hk) hfour

/-- Both signed component roots determine a square root of the orbit
discriminant. -/
theorem OrbitConnectingThreeRootWitness.orbitRootEquation
    {alpha beta gamma k omegaInv B C0 : K}
    (halpha : alpha ≠ 0)
    (hproduct : alpha * beta = k ^ 2)
    (w :
      OrbitConnectingThreeRootWitness
        alpha gamma k omegaInv B C0) :
    (w.plusRoot * w.minusRoot / alpha) ^ 2 =
      weightedOrbitDiscriminant alpha beta (w.middle - gamma) := by
  have hmul :=
    orbitComponentRadicand_mul_opposite_eq
      alpha beta k (w.middle - gamma) hproduct
  rw [← w.plusEquation, ← w.minusEquation] at hmul
  rw [div_pow]
  rw [show (w.plusRoot * w.minusRoot) ^ 2 =
      w.plusRoot ^ 2 * w.minusRoot ^ 2 by ring]
  rw [hmul]
  field_simp [halpha]

/-- If `2 ≠ 0`, `alpha ≠ 0`, `beta ≠ 0` and `alpha * beta = k ^ 2`, an
orbit-connecting three-root witness reconstructs a unit `s` such that the
weighted trace at `s ^ 2`, shifted by `gamma`, is the middle trace. -/
theorem exists_squareCosetParameter_of_orbitConnectingThreeRootWitness
    {alpha beta gamma k omegaInv B C0 : K}
    (h2 : (2 : K) ≠ 0)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hproduct : alpha * beta = k ^ 2)
    (w :
      OrbitConnectingThreeRootWitness
        alpha gamma k omegaInv B C0) :
    ∃ s : Kˣ,
      weightedSplitTorusTrace alpha beta (s ^ 2) + gamma =
        w.middle := by
  have horbit :=
    w.orbitRootEquation halpha hproduct
  -- Reconstruct from whichever component root is nonzero; the minus root is
  -- the component root for `-k` in place of `k`.
  rcases w.plus_ne_zero_or_minus_ne_zero
      h2 halpha hbeta hproduct with hplus | hminus
  · have hcomponent :
        w.middle - gamma + 2 * k ≠ 0 := by
      intro hzero
      apply hplus
      have hsq := w.plusEquation
      rw [orbitComponentRadicand, hzero, mul_zero] at hsq
      exact sq_eq_zero_iff.mp hsq
    let z :
        OrbitCosetBiquadraticSolution
          alpha beta k (w.middle - gamma) :=
      { orbitRoot := w.plusRoot * w.minusRoot / alpha
        componentRoot := w.plusRoot
        orbitEquation := horbit
        componentEquation := w.plusEquation }
    let reconstructed :=
      orbitCosetBiquadraticToWeightedOrbitQuartic
        alpha beta k (w.middle - gamma)
          h2 halpha hbeta hproduct hcomponent z
    let s : Kˣ :=
      Units.mk0 reconstructed.parameter
        reconstructed.parameter_ne_zero
    refine ⟨s, ?_⟩
    exact
      (weightedOrbitQuartic_eq_zero_iff_weightedSplitTorusTrace
        alpha beta gamma w.middle reconstructed.parameter
          reconstructed.parameter_ne_zero).mp
        reconstructed.equation
  · have hcomponent :
        w.middle - gamma + 2 * (-k) ≠ 0 := by
      intro hzero
      apply hminus
      have hsq := w.minusEquation
      have hrewrite :
          w.middle - gamma - 2 * k =
            w.middle - gamma + 2 * (-k) := by ring
      rw [orbitOppositeComponentRadicand, hrewrite,
        hzero, mul_zero] at hsq
      exact sq_eq_zero_iff.mp hsq
    have hproductNeg : alpha * beta = (-k) ^ 2 := by
      rw [hproduct]
      ring
    let z :
        OrbitCosetBiquadraticSolution
          alpha beta (-k) (w.middle - gamma) :=
      { orbitRoot := w.plusRoot * w.minusRoot / alpha
        componentRoot := w.minusRoot
        orbitEquation := horbit
        componentEquation := by
          -- `orbitComponentRadicand alpha (-k) (w.middle - gamma)` unfolds
          -- to `alpha * (w.middle - gamma + 2 * (-k))`; restate so that
          -- `w.minusEquation` and `ring` apply.
          change
            w.minusRoot ^ 2 =
              alpha * (w.middle - gamma + 2 * (-k))
          rw [w.minusEquation]
          simp only [orbitOppositeComponentRadicand]
          ring }
    let reconstructed :=
      orbitCosetBiquadraticToWeightedOrbitQuartic
        alpha beta (-k) (w.middle - gamma)
          h2 halpha hbeta hproductNeg hcomponent z
    let s : Kˣ :=
      Units.mk0 reconstructed.parameter
        reconstructed.parameter_ne_zero
    refine ⟨s, ?_⟩
    exact
      (weightedOrbitQuartic_eq_zero_iff_weightedSplitTorusTrace
        alpha beta gamma w.middle reconstructed.parameter
          reconstructed.parameter_ne_zero).mp
        reconstructed.equation

/-- For a good orbit-connecting witness with nonsquare scalar `omegaInv`, the
centered norm `centeredNorm B C0` of the middle trace is a nonsquare. -/
theorem
    centeredNorm_not_isSquare_of_orbitConnectingGoodThreeRootWitness
    {alpha gamma k omegaInv B C0 : K}
    (homegaInv : ¬ IsSquare omegaInv)
    (w :
      OrbitConnectingGoodThreeRootWitness
        alpha gamma k omegaInv B C0) :
    ¬ IsSquare (centeredNorm B C0 w.1.middle) := by
  have homegaInvZero : omegaInv ≠ 0 := by
    intro hzero
    apply homegaInv
    rw [hzero]
    exact IsSquare.zero
  have hnormZero : centeredNorm B C0 w.1.middle ≠ 0 := by
    intro hzero
    have hrootZero : w.1.thirdRoot ^ 2 = 0 := by
      rw [w.1.thirdEquation, hzero, mul_zero]
    exact w.2 (sq_eq_zero_iff.mp hrootZero)
  intro hnormSquare
  apply homegaInv
  have hrootSquare : IsSquare (w.1.thirdRoot ^ 2) :=
    ⟨w.1.thirdRoot, by ring⟩
  have hquotient :
      IsSquare
        (w.1.thirdRoot ^ 2 /
          centeredNorm B C0 w.1.middle) :=
    hrootSquare.div hnormSquare
  rw [w.1.thirdEquation] at hquotient
  simpa [hnormZero] using hquotient

end

end GenMarkoff.General.Cage
