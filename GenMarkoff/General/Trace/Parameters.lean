module

public import GenMarkoff.General.FiberDynamics
public import GenMarkoff.TraceCurve.ExceptionalRouting

@[expose] public section

/-!
# Shifted-trace parameters on a rotation fiber

For an ordered frame `(A,B,C)`, fix the coordinate carrying `A` at the value
`u`, put `t = s * u - A` and choose `q` with `q + q⁻¹ = t`.  This file
parametrizes the centered fiber conic by a torus parameter `h` (`torusPair`,
`fiberPair`, `fiberPoint1`, `fiberPoint2`) and shows that the rotation
`T_B ∘ T_C` acts by `h ↦ q² h`.

It then writes the affine traces of the two moving coordinates as shifted
expressions `α h + β / h + γ` in the torus parameter.  Both have the same
weight product `α β`, equal to `orderedTraceSigma A B C t`, but different
affine shifts:

* the first moving coordinate uses `orderedTraceGamma A B C t`;
* the second moving coordinate uses `orderedTraceGamma A C B t`.

These identities connect the rotation fibers with the shifted trace curves
of `GenMarkoff.TraceCurve`.
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

@[simp]
theorem fiberPoint1_x1 (a : Coefficients K) (u t q h : K) :
    (fiberPoint1 a u t q h).x1 = u :=
  rfl

@[simp]
theorem fiberPoint2_x2 (a : Coefficients K) (u t q h : K) :
    (fiberPoint2 a u t q h).x2 = u :=
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

/-- The affine rotation `T_B ∘ T_C` sends the torus parameter `h` to
`q² h`. -/
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
  -- `fiberPoint1 a u t q h` unfolds to `⟨u, (fiberPair ..).1, (fiberPair ..).2⟩`;
  -- restate so that `polynomial_fixed_first` rewrites the goal.
  change polynomial a
      ⟨u, (fiberPair a.a2 a.a3 u t q h).1,
        (fiberPair a.a2 a.a3 u t q h).2⟩ = 0
  rw [polynomial_fixed_first, ← hcoordinate]
  exact fiberPair_conic a.a2 a.a3 u t q h hD hq hh heigen

/-- The coefficient `α = s` of `h` in the trace `s * y - B` of the first
moving coordinate (`firstTrace_fiberPair`). -/
def actualAlpha (s : K) : K :=
  s

/-- The coefficient `β = s * P` of `h⁻¹` in the trace of the first moving
coordinate, where `P = centeredFiberProduct B C u t`. -/
def actualBeta (s B C u t : K) : K :=
  s * centeredFiberProduct B C u t

/-- The weight product `σ = α β`; the second moving coordinate has the same
product (`secondTrace_weight_product`). -/
def actualSigma (s B C u t : K) : K :=
  actualAlpha s * actualBeta s B C u t

/-- The affine shift `γ = s * m₁ - B` in the trace of the first moving
coordinate, whose coefficient is `B`; here `m` is `fiberCenter B C u t`. -/
def actualGammaFirst (s B C u t : K) : K :=
  s * (fiberCenter B C u t).1 - B

/-- The affine shift `s * m₂ - C` in the trace of the second moving
coordinate, whose coefficient is `C`; here `m` is `fiberCenter B C u t`. -/
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

/-- On the fiber `t = s * u - A`, the weight product `actualSigma` equals
`orderedTraceSigma A B C t`. -/
theorem actualSigma_eq_orderedTraceSigma
    (s A B C u t : K)
    (hcoordinateTrace : t = orderedTrace s A u) :
    actualSigma s B C u t = orderedTraceSigma A B C t := by
  have hsu : s * u = t + A := by
    rw [hcoordinateTrace, orderedTrace]
    ring
  rw [actualSigma, actualAlpha, actualBeta, centeredFiberProduct,
    centeredNorm, GenMarkoff.orderedTraceSigma]
  -- Regroup the two factors `s` with `u ^ 2` so that `hsu` rewrites `s * u`.
  rw [show
      s * (s * (u ^ 2 *
          (discriminant t + B ^ 2 + C ^ 2 + t * B * C) /
            discriminant t ^ 2)) =
        (s * u) ^ 2 *
          (discriminant t + B ^ 2 + C ^ 2 + t * B * C) /
            discriminant t ^ 2 by ring]
  rw [hsu]
  simp [discriminant]

/-- On the fiber `t = s * u - A`, the first affine shift equals
`orderedTraceGamma A B C t`. -/
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
  -- Regroup `s * (u * _)` as `(s * u) * _` so that `hsu` rewrites `s * u`.
  rw [show
      s * (u * (t * B + 2 * C) / discriminant t) - B =
        (s * u) * (t * B + 2 * C) / discriminant t - B by ring]
  rw [hsu]
  simp only [discriminant]
  field_simp [hD']
  ring

/-- On the fiber `t = s * u - A`, the second affine shift equals the
reverse-ordered `orderedTraceGamma A C B t`. -/
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
  -- Regroup `s * (u * _)` as `(s * u) * _` so that `hsu` rewrites `s * u`.
  rw [show
      s * (u * (t * C + 2 * B) / discriminant t) - C =
        (s * u) * (t * C + 2 * B) / discriminant t - C by ring]
  rw [hsu]
  simp only [discriminant]
  field_simp [hD']
  ring

end

end GenMarkoff.General
