import GenMarkoff.General.FiberDynamics
import GenMarkoff.TraceCurve.ExceptionalRouting

/-!
# Actual shifted-trace parameters for unequal coefficients

This file identifies the two directed adjacent traces on a general centered
rotation fiber.  For an ordered frame `(A,B,C)` and
`t = s * u - A`, the rotation `T_B ∘ T_C` acts on the torus parameter by
`h ↦ q² h`, where `q + q⁻¹ = t`.

The two adjacent directions have the same invariant weight product `sigma`
but different affine shifts:

* the first moving coordinate uses `orderedTraceGamma A B C t`;
* the second moving coordinate uses `orderedTraceGamma A C B t`.

This is the six-directed-axis bridge required before applying the existing
shifted trace-curve kernels.
-/

namespace GenMarkoff.General

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- Centered torus coordinates with eigenvalue `q`, product parameter `P`,
and torus parameter `h`. -/
def torusPair (q P h : K) : K × K :=
  (h + P / h, q * h + P / (q * h))

/-- One linear trace step multiplies the torus parameter by `q`. -/
theorem linearStep_torusPair
    (t q P h : K) (hq : q ≠ 0) (hh : h ≠ 0)
    (htrace : t = q + q⁻¹) :
    linearStep t (torusPair q P h) = torusPair q P (q * h) := by
  subst t
  apply Prod.ext
  · simp [linearStep, torusPair]
  · simp [linearStep, torusPair]
    field_simp [hq, hh]
    ring

/-- The squared linear trace step multiplies the torus parameter by `q²`. -/
theorem linearStep_sq_torusPair
    (t q P h : K) (hq : q ≠ 0) (hh : h ≠ 0)
    (htrace : t = q + q⁻¹) :
    linearStep t (linearStep t (torusPair q P h)) =
      torusPair q P (q ^ 2 * h) := by
  rw [linearStep_torusPair t q P h hq hh htrace]
  rw [linearStep_torusPair t q P (q * h) hq (mul_ne_zero hq hh) htrace]
  congr 1
  ring

/-- The torus pair has centered conic value `-D * P`. -/
theorem torusPair_conic
    (t q P h : K) (hq : q ≠ 0) (hh : h ≠ 0)
    (htrace : t = q + q⁻¹) :
    (torusPair q P h).1 ^ 2 + (torusPair q P h).2 ^ 2 -
        t * (torusPair q P h).1 * (torusPair q P h).2 =
      -discriminant t * P := by
  subst t
  simp [torusPair, discriminant]
  field_simp [hq, hh]
  ring

/-- A point of the ordered affine conic obtained from torus coordinates. -/
def fiberPair (B C u t q h : K) : K × K :=
  let m := fiberCenter B C u t
  let v := torusPair q (centeredFiberProduct B C u t) h
  (v.1 + m.1, v.2 + m.2)

/-- The parametrized point on a first-coordinate fiber. -/
def fiberPoint1 (a : Coefficients K) (u t q h : K) : Point K :=
  let v := fiberPair a.a2 a.a3 u t q h
  ⟨u, v.1, v.2⟩

/-- The parametrized point on a second-coordinate fiber.  Its moving
coordinates are ordered as `(x₃,x₁)`. -/
def fiberPoint2 (a : Coefficients K) (u t q h : K) : Point K :=
  let v := fiberPair a.a3 a.a1 u t q h
  ⟨v.2, u, v.1⟩

/-- The parametrized point on a third-coordinate fiber.  Its moving
coordinates are ordered as `(x₁,x₂)`. -/
def fiberPoint3 (a : Coefficients K) (u t q h : K) : Point K :=
  let v := fiberPair a.a1 a.a2 u t q h
  ⟨v.1, v.2, u⟩

@[simp]
theorem fiberPoint1_x1 (a : Coefficients K) (u t q h : K) :
    (fiberPoint1 a u t q h).x1 = u :=
  rfl

@[simp]
theorem fiberPoint2_x2 (a : Coefficients K) (u t q h : K) :
    (fiberPoint2 a u t q h).x2 = u :=
  rfl

@[simp]
theorem fiberPoint3_x3 (a : Coefficients K) (u t q h : K) :
    (fiberPoint3 a u t q h).x3 = u :=
  rfl

@[simp]
theorem movingCoordinates1_fiberPoint1
    (a : Coefficients K) (u t q h : K) :
    movingCoordinates1 (fiberPoint1 a u t q h) =
      fiberPair a.a2 a.a3 u t q h :=
  rfl

@[simp]
theorem movingCoordinates2_fiberPoint2
    (a : Coefficients K) (u t q h : K) :
    movingCoordinates2 (fiberPoint2 a u t q h) =
      fiberPair a.a3 a.a1 u t q h :=
  rfl

@[simp]
theorem movingCoordinates3_fiberPoint3
    (a : Coefficients K) (u t q h : K) :
    movingCoordinates3 (fiberPoint3 a u t q h) =
      fiberPair a.a1 a.a2 u t q h :=
  rfl

@[simp]
theorem fiberPair_fst (B C u t q h : K) :
    (fiberPair B C u t q h).1 =
      (torusPair q (centeredFiberProduct B C u t) h).1 +
        (fiberCenter B C u t).1 :=
  rfl

@[simp]
theorem fiberPair_snd (B C u t q h : K) :
    (fiberPair B C u t q h).2 =
      (torusPair q (centeredFiberProduct B C u t) h).2 +
        (fiberCenter B C u t).2 :=
  rfl

/-- The centered coordinates of `fiberPair` are its torus coordinates. -/
theorem centerCoordinates_fiberPair
    (B C u t q h : K) :
    centerCoordinates (fiberCenter B C u t) (fiberPair B C u t q h) =
      torusPair q (centeredFiberProduct B C u t) h := by
  ext <;> simp [centerCoordinates]

/-- The actual heterogeneous rotation sends the torus parameter to `q² h`. -/
theorem affineRotation_fiberPair
    (B C u t q h : K) (hD : discriminant t ≠ 0)
    (hq : q ≠ 0) (hh : h ≠ 0)
    (htrace : t = q + q⁻¹) :
    affineRotation B C u t (fiberPair B C u t q h) =
      fiberPair B C u t q (q ^ 2 * h) := by
  apply centerCoordinates_injective (fiberCenter B C u t)
  rw [centerCoordinates_affineRotation B C u t _ hD]
  rw [centerCoordinates_fiberPair]
  rw [linearStep_sq_torusPair t q
    (centeredFiberProduct B C u t) h hq hh htrace]
  rw [centerCoordinates_fiberPair]

/-- On the first-coordinate parametrization, `R₁` sends `h` to `q²h`. -/
theorem rotation1_fiberPoint1
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u) :
    rotation1 a (fiberPoint1 a u t q h) =
      fiberPoint1 a u t q (q ^ 2 * h) := by
  have hmoving :
      movingCoordinates1 (rotation1 a (fiberPoint1 a u t q h)) =
        fiberPair a.a2 a.a3 u t q (q ^ 2 * h) := by
    rw [movingCoordinates1_rotation1, fiberPoint1_x1, ← hcoordinate,
      movingCoordinates1_fiberPoint1]
    exact affineRotation_fiberPair a.a2 a.a3 u t q h hD hq hh heigen
  apply Point.ext
  · simp [rotation1, vieta2, vieta3]
  · exact congrArg Prod.fst hmoving
  · exact congrArg Prod.snd hmoving

/-- On the second-coordinate parametrization, `R₂` sends `h` to `q²h`. -/
theorem rotation2_fiberPoint2
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u) :
    rotation2 a (fiberPoint2 a u t q h) =
      fiberPoint2 a u t q (q ^ 2 * h) := by
  have hmoving :
      movingCoordinates2 (rotation2 a (fiberPoint2 a u t q h)) =
        fiberPair a.a3 a.a1 u t q (q ^ 2 * h) := by
    rw [movingCoordinates2_rotation2, fiberPoint2_x2, ← hcoordinate,
      movingCoordinates2_fiberPoint2]
    exact affineRotation_fiberPair a.a3 a.a1 u t q h hD hq hh heigen
  apply Point.ext
  · exact congrArg Prod.snd hmoving
  · simp [rotation2, vieta1, vieta3]
  · exact congrArg Prod.fst hmoving

/-- On the third-coordinate parametrization, `R₃` sends `h` to `q²h`. -/
theorem rotation3_fiberPoint3
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u) :
    rotation3 a (fiberPoint3 a u t q h) =
      fiberPoint3 a u t q (q ^ 2 * h) := by
  have hmoving :
      movingCoordinates3 (rotation3 a (fiberPoint3 a u t q h)) =
        fiberPair a.a1 a.a2 u t q (q ^ 2 * h) := by
    rw [movingCoordinates3_rotation3, fiberPoint3_x3, ← hcoordinate,
      movingCoordinates3_fiberPoint3]
    exact affineRotation_fiberPair a.a1 a.a2 u t q h hD hq hh heigen
  apply Point.ext
  · exact congrArg Prod.fst hmoving
  · exact congrArg Prod.snd hmoving
  · simp [rotation3, vieta1, vieta2]

/-- The parametrized pair lies on the ordered affine conic. -/
theorem fiberPair_conic
    (B C u t q h : K) (hD : discriminant t ≠ 0)
    (hq : q ≠ 0) (hh : h ≠ 0)
    (htrace : t = q + q⁻¹) :
    fiberConic B C u t
        (fiberPair B C u t q h).1
        (fiberPair B C u t q h).2 = 0 := by
  rw [fiberPair_fst, fiberPair_snd]
  rw [fiberConic_centered B C u t _ _ hD]
  rw [torusPair_conic t q (centeredFiberProduct B C u t) h hq hh htrace]
  rw [← discriminant_mul_centeredFiberProduct B C u t hD]
  ring

/-- The first-coordinate parametrization lies on the fixed generalized
Markoff surface. -/
theorem fiberPoint1_isSolution
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u) :
    IsSolution a (fiberPoint1 a u t q h) := by
  rw [IsSolution]
  change polynomial a
      ⟨u, (fiberPair a.a2 a.a3 u t q h).1,
        (fiberPair a.a2 a.a3 u t q h).2⟩ = 0
  rw [polynomial_fixed_first, ← hcoordinate]
  exact fiberPair_conic a.a2 a.a3 u t q h hD hq hh heigen

/-- The second-coordinate parametrization lies on the fixed generalized
Markoff surface. -/
theorem fiberPoint2_isSolution
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u) :
    IsSolution a (fiberPoint2 a u t q h) := by
  rw [IsSolution]
  change polynomial a
      ⟨(fiberPair a.a3 a.a1 u t q h).2, u,
        (fiberPair a.a3 a.a1 u t q h).1⟩ = 0
  rw [polynomial_fixed_second, ← hcoordinate]
  exact fiberPair_conic a.a3 a.a1 u t q h hD hq hh heigen

/-- The third-coordinate parametrization lies on the fixed generalized
Markoff surface. -/
theorem fiberPoint3_isSolution
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (heigen : t = q + q⁻¹)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u) :
    IsSolution a (fiberPoint3 a u t q h) := by
  rw [IsSolution]
  change polynomial a
      ⟨(fiberPair a.a1 a.a2 u t q h).1,
        (fiberPair a.a1 a.a2 u t q h).2, u⟩ = 0
  rw [polynomial_fixed_third, ← hcoordinate]
  exact fiberPair_conic a.a1 a.a2 u t q h hD hq hh heigen

/-- First directed trace weight. -/
def actualAlpha (s : K) : K :=
  s

/-- Reciprocal first-directed trace weight. -/
def actualBeta (s B C u t : K) : K :=
  s * centeredFiberProduct B C u t

/-- Invariant product of the two first-directed weights. -/
def actualSigma (s B C u t : K) : K :=
  actualAlpha s * actualBeta s B C u t

/-- Affine shift for the first moving coordinate, whose coefficient is `B`. -/
def actualGammaFirst (s B C u t : K) : K :=
  s * (fiberCenter B C u t).1 - B

/-- Affine shift for the second moving coordinate, whose coefficient is
`C`. -/
def actualGammaSecond (s B C u t : K) : K :=
  s * (fiberCenter B C u t).2 - C

/-- Exact shifted trace formula for the first moving coordinate. -/
theorem firstTrace_fiberPair
    (s B C u t q h : K) (hh : h ≠ 0) :
    s * (fiberPair B C u t q h).1 - B =
      actualAlpha s * h + actualBeta s B C u t / h +
        actualGammaFirst s B C u t := by
  simp [fiberPair, torusPair, actualAlpha, actualBeta, actualGammaFirst]
  field_simp [hh]
  ring

/-- Exact shifted trace formula for the second moving coordinate. -/
theorem secondTrace_fiberPair
    (s B C u t q h : K) (hq : q ≠ 0) (hh : h ≠ 0) :
    s * (fiberPair B C u t q h).2 - C =
      (s * q) * h +
        (s * centeredFiberProduct B C u t / q) / h +
        actualGammaSecond s B C u t := by
  simp [fiberPair, torusPair, actualGammaSecond]
  field_simp [hq, hh]
  ring

/-- Both directed traces have the same invariant weight product. -/
theorem secondTrace_weight_product
    (s B C u t q : K) (hq : q ≠ 0) :
    (s * q) * (s * centeredFiberProduct B C u t / q) =
      actualSigma s B C u t := by
  rw [actualSigma, actualAlpha, actualBeta]
  field_simp [hq]

/-- The actual invariant weight product is the ordered candidate `sigma`. -/
theorem actualSigma_eq_orderedTraceSigma
    (s A B C u t : K)
    (hcoordinateTrace : t = orderedTrace s A u) :
    actualSigma s B C u t = orderedTraceSigma A B C t := by
  have hsu : s * u = t + A := by
    rw [hcoordinateTrace, orderedTrace]
    ring
  rw [actualSigma, actualAlpha, actualBeta, centeredFiberProduct,
    centeredNorm, GenMarkoff.orderedTraceSigma]
  rw [show
      s * (s * (u ^ 2 *
          (discriminant t + B ^ 2 + C ^ 2 + t * B * C) /
            discriminant t ^ 2)) =
        (s * u) ^ 2 *
          (discriminant t + B ^ 2 + C ^ 2 + t * B * C) /
            discriminant t ^ 2 by ring]
  rw [hsu]
  simp [discriminant]

/-- The two directed adjacent traces have the same weight product, and that
common product is exactly the ordered shifted-cover parameter `sigma`. -/
theorem directedTrace_weightProducts_eq_orderedTraceSigma
    (s A B C u t q : K) (hq : q ≠ 0)
    (hcoordinateTrace : t = orderedTrace s A u) :
    actualAlpha s * actualBeta s B C u t =
        orderedTraceSigma A B C t ∧
      (s * q) * (s * centeredFiberProduct B C u t / q) =
        orderedTraceSigma A B C t := by
  constructor
  · simpa [actualSigma] using
      actualSigma_eq_orderedTraceSigma s A B C u t hcoordinateTrace
  · rw [secondTrace_weight_product s B C u t q hq]
    exact actualSigma_eq_orderedTraceSigma s A B C u t hcoordinateTrace

/-- The first actual affine shift is the first ordered candidate `gamma`. -/
theorem actualGammaFirst_eq_orderedTraceGamma
    (s A B C u t : K) (hD : discriminant t ≠ 0)
    (hcoordinateTrace : t = orderedTrace s A u) :
    actualGammaFirst s B C u t = orderedTraceGamma A B C t := by
  have hsu : s * u = t + A := by
    rw [hcoordinateTrace, orderedTrace]
    ring
  have hD' : t ^ 2 - 4 ≠ 0 := by
    simpa [discriminant] using hD
  simp only [actualGammaFirst, fiberCenter, GenMarkoff.orderedTraceGamma,
    GenMarkoff.eval_orderedTraceShiftPolynomial]
  rw [show
      s * (u * (t * B + 2 * C) / discriminant t) - B =
        (s * u) * (t * B + 2 * C) / discriminant t - B by ring]
  rw [hsu]
  simp only [discriminant]
  field_simp [hD']
  ring

/-- The second actual affine shift is the reverse ordered candidate `gamma`. -/
theorem actualGammaSecond_eq_orderedTraceGamma
    (s A B C u t : K) (hD : discriminant t ≠ 0)
    (hcoordinateTrace : t = orderedTrace s A u) :
    actualGammaSecond s B C u t = orderedTraceGamma A C B t := by
  have hsu : s * u = t + A := by
    rw [hcoordinateTrace, orderedTrace]
    ring
  have hD' : t ^ 2 - 4 ≠ 0 := by
    simpa [discriminant] using hD
  simp only [actualGammaSecond, fiberCenter, GenMarkoff.orderedTraceGamma,
    GenMarkoff.eval_orderedTraceShiftPolynomial]
  rw [show
      s * (u * (t * C + 2 * B) / discriminant t) - C =
        (s * u) * (t * C + 2 * B) / discriminant t - C by ring]
  rw [hsu]
  simp only [discriminant]
  field_simp [hD']
  ring

/-- On a first-coordinate fiber, the `x₂` trace has the ordered parameters
for the directed frame `(a₁,a₂,a₃)`. -/
theorem orderedTrace_fiberPoint1_x2
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hh : h ≠ 0)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u) :
    orderedTrace a.multiplier a.a2 (fiberPoint1 a u t q h).x2 =
      actualAlpha a.multiplier * h +
        actualBeta a.multiplier a.a2 a.a3 u t / h +
        orderedTraceGamma a.a1 a.a2 a.a3 t := by
  change
    a.multiplier * (fiberPair a.a2 a.a3 u t q h).1 - a.a2 =
      actualAlpha a.multiplier * h +
        actualBeta a.multiplier a.a2 a.a3 u t / h +
        orderedTraceGamma a.a1 a.a2 a.a3 t
  rw [firstTrace_fiberPair a.multiplier a.a2 a.a3 u t q h hh]
  rw [actualGammaFirst_eq_orderedTraceGamma
    a.multiplier a.a1 a.a2 a.a3 u t hD hcoordinate]

/-- On a first-coordinate fiber, the `x₃` trace has the reverse ordered
parameters for the directed frame `(a₁,a₃,a₂)`. -/
theorem orderedTrace_fiberPoint1_x3
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (hcoordinate : t = orderedTrace a.multiplier a.a1 u) :
    orderedTrace a.multiplier a.a3 (fiberPoint1 a u t q h).x3 =
      (a.multiplier * q) * h +
        (a.multiplier * centeredFiberProduct a.a2 a.a3 u t / q) / h +
        orderedTraceGamma a.a1 a.a3 a.a2 t := by
  change
    a.multiplier * (fiberPair a.a2 a.a3 u t q h).2 - a.a3 =
      (a.multiplier * q) * h +
        (a.multiplier * centeredFiberProduct a.a2 a.a3 u t / q) / h +
        orderedTraceGamma a.a1 a.a3 a.a2 t
  rw [secondTrace_fiberPair a.multiplier a.a2 a.a3 u t q h hq hh]
  rw [actualGammaSecond_eq_orderedTraceGamma
    a.multiplier a.a1 a.a2 a.a3 u t hD hcoordinate]

/-- On a second-coordinate fiber, the `x₃` trace has the ordered parameters
for the directed frame `(a₂,a₃,a₁)`. -/
theorem orderedTrace_fiberPoint2_x3
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hh : h ≠ 0)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u) :
    orderedTrace a.multiplier a.a3 (fiberPoint2 a u t q h).x3 =
      actualAlpha a.multiplier * h +
        actualBeta a.multiplier a.a3 a.a1 u t / h +
        orderedTraceGamma a.a2 a.a3 a.a1 t := by
  change
    a.multiplier * (fiberPair a.a3 a.a1 u t q h).1 - a.a3 =
      actualAlpha a.multiplier * h +
        actualBeta a.multiplier a.a3 a.a1 u t / h +
        orderedTraceGamma a.a2 a.a3 a.a1 t
  rw [firstTrace_fiberPair a.multiplier a.a3 a.a1 u t q h hh]
  rw [actualGammaFirst_eq_orderedTraceGamma
    a.multiplier a.a2 a.a3 a.a1 u t hD hcoordinate]

/-- On a second-coordinate fiber, the `x₁` trace has the reverse ordered
parameters for the directed frame `(a₂,a₁,a₃)`. -/
theorem orderedTrace_fiberPoint2_x1
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (hcoordinate : t = orderedTrace a.multiplier a.a2 u) :
    orderedTrace a.multiplier a.a1 (fiberPoint2 a u t q h).x1 =
      (a.multiplier * q) * h +
        (a.multiplier * centeredFiberProduct a.a3 a.a1 u t / q) / h +
        orderedTraceGamma a.a2 a.a1 a.a3 t := by
  change
    a.multiplier * (fiberPair a.a3 a.a1 u t q h).2 - a.a1 =
      (a.multiplier * q) * h +
        (a.multiplier * centeredFiberProduct a.a3 a.a1 u t / q) / h +
        orderedTraceGamma a.a2 a.a1 a.a3 t
  rw [secondTrace_fiberPair a.multiplier a.a3 a.a1 u t q h hq hh]
  rw [actualGammaSecond_eq_orderedTraceGamma
    a.multiplier a.a2 a.a3 a.a1 u t hD hcoordinate]

/-- On a third-coordinate fiber, the `x₁` trace has the ordered parameters
for the directed frame `(a₃,a₁,a₂)`. -/
theorem orderedTrace_fiberPoint3_x1
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hh : h ≠ 0)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u) :
    orderedTrace a.multiplier a.a1 (fiberPoint3 a u t q h).x1 =
      actualAlpha a.multiplier * h +
        actualBeta a.multiplier a.a1 a.a2 u t / h +
        orderedTraceGamma a.a3 a.a1 a.a2 t := by
  change
    a.multiplier * (fiberPair a.a1 a.a2 u t q h).1 - a.a1 =
      actualAlpha a.multiplier * h +
        actualBeta a.multiplier a.a1 a.a2 u t / h +
        orderedTraceGamma a.a3 a.a1 a.a2 t
  rw [firstTrace_fiberPair a.multiplier a.a1 a.a2 u t q h hh]
  rw [actualGammaFirst_eq_orderedTraceGamma
    a.multiplier a.a3 a.a1 a.a2 u t hD hcoordinate]

/-- On a third-coordinate fiber, the `x₂` trace has the reverse ordered
parameters for the directed frame `(a₃,a₂,a₁)`. -/
theorem orderedTrace_fiberPoint3_x2
    (a : Coefficients K) (u t q h : K)
    (hD : discriminant t ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (hcoordinate : t = orderedTrace a.multiplier a.a3 u) :
    orderedTrace a.multiplier a.a2 (fiberPoint3 a u t q h).x2 =
      (a.multiplier * q) * h +
        (a.multiplier * centeredFiberProduct a.a1 a.a2 u t / q) / h +
        orderedTraceGamma a.a3 a.a2 a.a1 t := by
  change
    a.multiplier * (fiberPair a.a1 a.a2 u t q h).2 - a.a2 =
      (a.multiplier * q) * h +
        (a.multiplier * centeredFiberProduct a.a1 a.a2 u t / q) / h +
        orderedTraceGamma a.a3 a.a2 a.a1 t
  rw [secondTrace_fiberPair a.multiplier a.a1 a.a2 u t q h hq hh]
  rw [actualGammaSecond_eq_orderedTraceGamma
    a.multiplier a.a3 a.a1 a.a2 u t hD hcoordinate]

end

end GenMarkoff.General
