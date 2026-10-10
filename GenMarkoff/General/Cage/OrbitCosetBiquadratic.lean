import GenMarkoff.General.Cage.Connecting.IncidenceAlgebra
import BGS.Markoff.TraceCurve.Geometry

/-!
# A biquadratic model for a square-product orbit coset

Suppose that the two weights in a shifted split-torus trace satisfy
`alpha * beta = k ^ 2`.  After writing `U = T - gamma`, the equation

`weightedSplitTorusTrace alpha beta (s ^ 2) + gamma = T`

clears to the reciprocal quartic

`alpha * s ^ 4 - U * s ^ 2 + beta = 0`

(`weightedOrbitQuartic_eq_zero_iff_weightedSplitTorusTrace`).  This file
solves the quartic from a pair of signed square roots

`r ^ 2 = U ^ 2 - 4 * alpha * beta`,
`l ^ 2 = alpha * (U + 2 * k)`

(an `OrbitCosetBiquadraticSolution`): away from the component divisor
`U + 2 * k = 0`, and for `2 ≠ 0`, `alpha ≠ 0`, `beta ≠ 0`, the parameter

`s = (l ^ 2 + alpha * r) / (2 * alpha * l)`

is a nonzero root of the quartic
(`orbitCosetBiquadraticToWeightedOrbitQuartic`).
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The reciprocal quartic obtained from a shifted weighted trace evaluated
at a square torus parameter. -/
def weightedOrbitQuartic
    (alpha beta U s : K) : K :=
  alpha * s ^ 4 - U * s ^ 2 + beta

/-- The discriminant radicand of the weighted orbit quartic. -/
def weightedOrbitDiscriminant
    (alpha beta U : K) : K :=
  U ^ 2 - 4 * alpha * beta

/-- The second radicand which separates the two components when
`alpha * beta` is the square `k ^ 2`. -/
def orbitComponentRadicand
    (alpha k U : K) : K :=
  alpha * (U + 2 * k)

/-- A nonzero parameter satisfying the weighted orbit quartic. -/
structure WeightedOrbitQuarticSolution
    (alpha beta U : K) where
  parameter : K
  parameter_ne_zero : parameter ≠ 0
  equation : weightedOrbitQuartic alpha beta U parameter = 0

@[ext]
theorem WeightedOrbitQuarticSolution.ext
    {alpha beta U : K}
    {x y : WeightedOrbitQuarticSolution alpha beta U}
    (hparameter : x.parameter = y.parameter) :
    x = y := by
  cases x
  cases y
  simp_all

/-- A signed pair of roots of the orbit-discriminant and component
radicands. -/
structure OrbitCosetBiquadraticSolution
    (alpha beta k U : K) where
  orbitRoot : K
  componentRoot : K
  orbitEquation :
    orbitRoot ^ 2 = weightedOrbitDiscriminant alpha beta U
  componentEquation :
    componentRoot ^ 2 = orbitComponentRadicand alpha k U

@[ext]
theorem OrbitCosetBiquadraticSolution.ext
    {alpha beta k U : K}
    {x y : OrbitCosetBiquadraticSolution alpha beta k U}
    (horbitRoot : x.orbitRoot = y.orbitRoot)
    (hcomponentRoot : x.componentRoot = y.componentRoot) :
    x = y := by
  cases x
  cases y
  simp_all

/-- Reconstruction of the quartic parameter from the two signed square
roots. -/
def reconstructedWeightedOrbitParameter
    (alpha r l : K) : K :=
  (l ^ 2 + alpha * r) / (2 * alpha * l)

/-- Clearing the denominator of a weighted trace evaluated at `s ^ 2`
gives exactly the weighted orbit quartic. -/
theorem weightedOrbitQuartic_eq_zero_iff_weightedSplitTorusTrace
    (alpha beta gamma T s : K) (hs : s ≠ 0) :
    weightedOrbitQuartic alpha beta (T - gamma) s = 0 ↔
      weightedSplitTorusTrace alpha beta ((Units.mk0 s hs) ^ 2) +
          gamma = T := by
  simp only [weightedOrbitQuartic, weightedSplitTorusTrace,
    Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
    Units.val_mk0]
  field_simp [hs]
  constructor <;> intro h <;> linear_combination h

/-- A biquadratic solution has nonzero component root away from the
component divisor. -/
theorem OrbitCosetBiquadraticSolution.componentRoot_ne_zero
    {alpha beta k U : K}
    (z : OrbitCosetBiquadraticSolution alpha beta k U)
    (halpha : alpha ≠ 0) (hcomponent : U + 2 * k ≠ 0) :
    z.componentRoot ≠ 0 := by
  intro hzero
  have hsquare : z.componentRoot ^ 2 = 0 := by rw [hzero]; simp
  rw [z.componentEquation, orbitComponentRadicand] at hsquare
  exact (mul_ne_zero halpha hcomponent) hsquare

/-- The square of the reconstructed parameter is `(U + r) / (2 * alpha)`,
where `r` is the orbit root. -/
theorem reconstructedWeightedOrbitParameter_sq
    {alpha beta k U : K}
    (h2 : (2 : K) ≠ 0) (halpha : alpha ≠ 0)
    (hproduct : alpha * beta = k ^ 2)
    (hcomponent : U + 2 * k ≠ 0)
    (z : OrbitCosetBiquadraticSolution alpha beta k U) :
    reconstructedWeightedOrbitParameter
        alpha z.orbitRoot z.componentRoot ^ 2 =
      (U + z.orbitRoot) / (2 * alpha) := by
  have hl : z.componentRoot ≠ 0 :=
    z.componentRoot_ne_zero halpha hcomponent
  simp only [reconstructedWeightedOrbitParameter]
  field_simp [h2, halpha, hl, hcomponent]
  rw [z.componentEquation, orbitComponentRadicand]
  have horbit :
      z.orbitRoot ^ 2 = U ^ 2 - 4 * k ^ 2 := by
    rw [z.orbitEquation, weightedOrbitDiscriminant]
    rw [← hproduct]
    ring
  linear_combination alpha ^ 2 * horbit

/-- Reconstruction from a biquadratic pair satisfies the original
quartic. -/
theorem reconstructedWeightedOrbitParameter_equation
    {alpha beta k U : K}
    (h2 : (2 : K) ≠ 0) (halpha : alpha ≠ 0)
    (hproduct : alpha * beta = k ^ 2)
    (hcomponent : U + 2 * k ≠ 0)
    (z : OrbitCosetBiquadraticSolution alpha beta k U) :
    weightedOrbitQuartic alpha beta U
        (reconstructedWeightedOrbitParameter
          alpha z.orbitRoot z.componentRoot) = 0 := by
  rw [weightedOrbitQuartic]
  -- Rewrite `s ^ 4` as `(s ^ 2) ^ 2` so that
  -- `reconstructedWeightedOrbitParameter_sq` applies.
  rw [show
      reconstructedWeightedOrbitParameter
          alpha z.orbitRoot z.componentRoot ^ 4 =
        (reconstructedWeightedOrbitParameter
          alpha z.orbitRoot z.componentRoot ^ 2) ^ 2 by ring]
  rw [reconstructedWeightedOrbitParameter_sq
    h2 halpha hproduct hcomponent z]
  field_simp [h2, halpha]
  have horbit := z.orbitEquation
  simp only [weightedOrbitDiscriminant] at horbit
  linear_combination horbit

/-- Reconstruction from a biquadratic pair gives a nonzero parameter when
`beta ≠ 0`. -/
theorem reconstructedWeightedOrbitParameter_ne_zero
    {alpha beta k U : K}
    (h2 : (2 : K) ≠ 0) (halpha : alpha ≠ 0)
    (hbeta : beta ≠ 0)
    (hproduct : alpha * beta = k ^ 2)
    (hcomponent : U + 2 * k ≠ 0)
    (z : OrbitCosetBiquadraticSolution alpha beta k U) :
    reconstructedWeightedOrbitParameter
        alpha z.orbitRoot z.componentRoot ≠ 0 := by
  intro hzero
  have hequation :=
    reconstructedWeightedOrbitParameter_equation
      h2 halpha hproduct hcomponent z
  rw [hzero] at hequation
  have : beta = 0 := by
    simpa [weightedOrbitQuartic] using hequation
  exact hbeta this

/-- Reconstruct a nonzero quartic parameter from a signed biquadratic
solution away from the component divisor. -/
def orbitCosetBiquadraticToWeightedOrbitQuartic
    (alpha beta k U : K)
    (h2 : (2 : K) ≠ 0) (halpha : alpha ≠ 0)
    (hbeta : beta ≠ 0)
    (hproduct : alpha * beta = k ^ 2)
    (hcomponent : U + 2 * k ≠ 0) :
    OrbitCosetBiquadraticSolution alpha beta k U →
      WeightedOrbitQuarticSolution alpha beta U :=
  fun z =>
    { parameter :=
        reconstructedWeightedOrbitParameter
          alpha z.orbitRoot z.componentRoot
      parameter_ne_zero :=
        reconstructedWeightedOrbitParameter_ne_zero
          h2 halpha hbeta hproduct hcomponent z
      equation :=
        reconstructedWeightedOrbitParameter_equation
          h2 halpha hproduct hcomponent z }

end

end GenMarkoff.General.Cage
