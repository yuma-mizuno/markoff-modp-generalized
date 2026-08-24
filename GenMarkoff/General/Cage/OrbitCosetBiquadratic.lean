import GenMarkoff.General.Cage.ConnectingIncidenceAlgebra
import BGS.Markoff.TraceCurve.Geometry

/-!
# A biquadratic model for a square-product orbit coset

Suppose that the two weights in a shifted split-torus trace satisfy
`alpha * beta = k ^ 2`.  After writing `U = T - gamma`, the equation

`weightedSplitTorusTrace alpha beta (s ^ 2) + gamma = T`

clears to the reciprocal quartic

`alpha * s ^ 4 - U * s ^ 2 + beta = 0`.

Away from the component divisor `U + 2 * k = 0`, this quartic is equivalent
to the two independent square-root equations

`r ^ 2 = U ^ 2 - 4 * alpha * beta`,
`l ^ 2 = alpha * (U + 2 * k)`.

The forward coordinates and their inverse are

`r = 2 * alpha * s ^ 2 - U`,
`l = alpha * s + k / s`,
`s = (l ^ 2 + alpha * r) / (2 * alpha * l)`.

The signs of both square roots are retained in the structures below.  Thus
the final equivalence is an equivalence of witness-bearing solution types,
not merely an existence statement.
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

/-- The first square-root coordinate attached to a quartic parameter. -/
def weightedOrbitRoot
    (alpha U s : K) : K :=
  2 * alpha * s ^ 2 - U

/-- The component square-root coordinate attached to a nonzero quartic
parameter. -/
def weightedOrbitComponentRoot
    (alpha k s : K) : K :=
  alpha * s + k / s

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

/-- The first forward coordinate satisfies the orbit-discriminant
equation. -/
theorem weightedOrbitRoot_sq
    (alpha beta k U s : K)
    (_hproduct : alpha * beta = k ^ 2)
    (hequation : weightedOrbitQuartic alpha beta U s = 0) :
    weightedOrbitRoot alpha U s ^ 2 =
      weightedOrbitDiscriminant alpha beta U := by
  simp only [weightedOrbitRoot, weightedOrbitDiscriminant,
    weightedOrbitQuartic] at hequation ⊢
  linear_combination 4 * alpha * hequation

/-- The second forward coordinate satisfies the component-radicand
equation. -/
theorem weightedOrbitComponentRoot_sq
    (alpha beta k U s : K) (hs : s ≠ 0)
    (hproduct : alpha * beta = k ^ 2)
    (hequation : weightedOrbitQuartic alpha beta U s = 0) :
    weightedOrbitComponentRoot alpha k s ^ 2 =
      orbitComponentRadicand alpha k U := by
  have htrace : alpha * s ^ 2 + beta / s ^ 2 = U := by
    simp only [weightedOrbitQuartic] at hequation
    field_simp [hs]
    linear_combination hequation
  calc
    weightedOrbitComponentRoot alpha k s ^ 2 =
        alpha * (alpha * s ^ 2 + beta / s ^ 2 + 2 * k) := by
      simp only [weightedOrbitComponentRoot]
      field_simp [hs]
      linear_combination -1 * hproduct
    _ = orbitComponentRadicand alpha k U := by
      rw [htrace]
      rfl

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

/-- The reconstructed parameter has the expected square. -/
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

/-- Reconstruction also gives a nonzero parameter.  The nonzero constant
term `beta` rules out zero once the quartic equation is known. -/
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

/-- Send a nonzero quartic parameter to its two signed square roots. -/
def weightedOrbitQuarticToBiquadratic
    (alpha beta k U : K)
    (hproduct : alpha * beta = k ^ 2) :
    WeightedOrbitQuarticSolution alpha beta U →
      OrbitCosetBiquadraticSolution alpha beta k U :=
  fun z =>
    { orbitRoot := weightedOrbitRoot alpha U z.parameter
      componentRoot :=
        weightedOrbitComponentRoot alpha k z.parameter
      orbitEquation :=
        weightedOrbitRoot_sq alpha beta k U z.parameter
          hproduct z.equation
      componentEquation :=
        weightedOrbitComponentRoot_sq alpha beta k U z.parameter
          z.parameter_ne_zero hproduct z.equation }

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

/-- Applying the reconstruction formula to the roots obtained from a
quartic parameter recovers that parameter. -/
theorem reconstructedWeightedOrbitParameter_forward
    (alpha beta k U s : K)
    (h2 : (2 : K) ≠ 0) (halpha : alpha ≠ 0)
    (hs : s ≠ 0)
    (hproduct : alpha * beta = k ^ 2)
    (hcomponent : U + 2 * k ≠ 0)
    (hequation : weightedOrbitQuartic alpha beta U s = 0) :
    reconstructedWeightedOrbitParameter alpha
        (weightedOrbitRoot alpha U s)
        (weightedOrbitComponentRoot alpha k s) = s := by
  let z : OrbitCosetBiquadraticSolution alpha beta k U :=
    { orbitRoot := weightedOrbitRoot alpha U s
      componentRoot := weightedOrbitComponentRoot alpha k s
      orbitEquation :=
        weightedOrbitRoot_sq alpha beta k U s hproduct hequation
      componentEquation :=
        weightedOrbitComponentRoot_sq alpha beta k U s hs
          hproduct hequation }
  have hl :
      weightedOrbitComponentRoot alpha k s ≠ 0 :=
    z.componentRoot_ne_zero halpha hcomponent
  apply (div_eq_iff
    (mul_ne_zero (mul_ne_zero h2 halpha) hl)).2
  rw [weightedOrbitComponentRoot_sq alpha beta k U s hs
    hproduct hequation]
  simp only [orbitComponentRadicand, weightedOrbitRoot,
    weightedOrbitComponentRoot]
  field_simp [hs]
  ring

/-- Reconstructing a parameter from a biquadratic solution and then taking
its first root recovers the prescribed orbit root. -/
theorem weightedOrbitRoot_reconstructed
    {alpha beta k U : K}
    (h2 : (2 : K) ≠ 0) (halpha : alpha ≠ 0)
    (hproduct : alpha * beta = k ^ 2)
    (hcomponent : U + 2 * k ≠ 0)
    (z : OrbitCosetBiquadraticSolution alpha beta k U) :
    weightedOrbitRoot alpha U
        (reconstructedWeightedOrbitParameter
          alpha z.orbitRoot z.componentRoot) =
      z.orbitRoot := by
  rw [weightedOrbitRoot]
  rw [reconstructedWeightedOrbitParameter_sq
    h2 halpha hproduct hcomponent z]
  field_simp [h2, halpha]
  ring

/-- Reconstructing a parameter from a biquadratic solution and then taking
its component root recovers the prescribed signed component root. -/
theorem weightedOrbitComponentRoot_reconstructed
    {alpha beta k U : K}
    (h2 : (2 : K) ≠ 0) (halpha : alpha ≠ 0)
    (hbeta : beta ≠ 0)
    (hproduct : alpha * beta = k ^ 2)
    (hcomponent : U + 2 * k ≠ 0)
    (z : OrbitCosetBiquadraticSolution alpha beta k U) :
    weightedOrbitComponentRoot alpha k
        (reconstructedWeightedOrbitParameter
          alpha z.orbitRoot z.componentRoot) =
      z.componentRoot := by
  have hs :
      reconstructedWeightedOrbitParameter
          alpha z.orbitRoot z.componentRoot ≠ 0 :=
    reconstructedWeightedOrbitParameter_ne_zero
      h2 halpha hbeta hproduct hcomponent z
  have hl : z.componentRoot ≠ 0 :=
    z.componentRoot_ne_zero halpha hcomponent
  simp only [weightedOrbitComponentRoot]
  field_simp [hs, hl]
  rw [reconstructedWeightedOrbitParameter_sq
    h2 halpha hproduct hcomponent z]
  simp only [reconstructedWeightedOrbitParameter]
  field_simp [h2, halpha, hl]
  rw [z.componentEquation, orbitComponentRadicand]
  ring

/-- Away from `U + 2 * k = 0`, the nonzero weighted-orbit quartic is
equivalent to the witness-bearing biquadratic system. -/
def weightedOrbitQuarticSolutionEquivOrbitCosetBiquadratic
    (alpha beta k U : K)
    (h2 : (2 : K) ≠ 0)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (_hk : k ≠ 0)
    (hproduct : alpha * beta = k ^ 2)
    (hcomponent : U + 2 * k ≠ 0) :
    WeightedOrbitQuarticSolution alpha beta U ≃
      OrbitCosetBiquadraticSolution alpha beta k U where
  toFun :=
    weightedOrbitQuarticToBiquadratic
      alpha beta k U hproduct
  invFun :=
    orbitCosetBiquadraticToWeightedOrbitQuartic
      alpha beta k U h2 halpha hbeta hproduct hcomponent
  left_inv := by
    intro z
    apply WeightedOrbitQuarticSolution.ext
    exact reconstructedWeightedOrbitParameter_forward
      alpha beta k U z.parameter h2 halpha z.parameter_ne_zero
        hproduct hcomponent z.equation
  right_inv := by
    intro z
    apply OrbitCosetBiquadraticSolution.ext
    · exact weightedOrbitRoot_reconstructed
        h2 halpha hproduct hcomponent z
    · exact weightedOrbitComponentRoot_reconstructed
        h2 halpha hbeta hproduct hcomponent z

end

end GenMarkoff.General.Cage
