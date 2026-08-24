import GenMarkoff.Symmetric.FiberDynamics
import GenMarkoff.TraceCurve.ExceptionalRouting

/-!
# Actual shifted trace parameters in the symmetric family

This module identifies the parameters produced by the affine diagonalization
with the ordered parameters already used by the shifted-cover development.
The identification is an equality theorem, not merely a candidate formula.
-/

namespace GenMarkoff.Symmetric

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The nonparabolic discriminant. -/
def discriminant (t : K) : K :=
  t ^ 2 - 4

theorem ne_two_of_discriminant_ne_zero {t : K}
    (hD : discriminant t ≠ 0) : t ≠ 2 := by
  intro ht
  subst t
  norm_num [discriminant] at hD

theorem ne_neg_two_of_discriminant_ne_zero {t : K}
    (hD : discriminant t ≠ 0) : t ≠ -2 := by
  intro ht
  subst t
  norm_num [discriminant] at hD

/-- The product of the two centered eigen-coordinates on the affine conic. -/
def centeredFiberProduct (c u t : K) : K :=
  u ^ 2 * (t + c ^ 2 - 2) / ((t - 2) * discriminant t)

/-- The first adjacent-trace weight in the chosen torus parametrization. -/
def actualAlpha (c : K) : K :=
  multiplier c

/-- The second adjacent-trace weight in the chosen torus parametrization. -/
def actualBeta (c u t : K) : K :=
  multiplier c * centeredFiberProduct c u t

/-- The product of the two actual adjacent-trace weights. -/
def actualSigma (c u t : K) : K :=
  actualAlpha c * actualBeta c u t

/-- The affine constant in the adjacent trace. -/
def actualGamma (c u t : K) : K :=
  multiplier c * fiberCenter c u t - c

/-- Centered torus coordinates with eigenvalue `q` and parameter `h`. -/
def torusPair (q P h : K) : K × K :=
  (h + P / h, q * h + P / (q * h))

/-- The linear half-step multiplies the torus parameter by `q`. -/
theorem linearStep_torusPair
    (t q P h : K) (hq : q ≠ 0) (hh : h ≠ 0)
    (htrace : t = q + q⁻¹) :
    linearStep t (torusPair q P h) = torusPair q P (q * h) := by
  subst t
  ext <;>
    simp [linearStep, torusPair] <;>
    field_simp [hq, hh] <;>
    ring

/-- The centered torus pair satisfies the conic with constant
`-(t²-4)P`. -/
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

/-- A point in the first-coordinate fiber obtained from torus coordinates. -/
def fiberPoint (c u t q h : K) : Point K :=
  let m := fiberCenter c u t
  let v := torusPair q (centeredFiberProduct c u t) h
  ⟨u, v.1 + m, v.2 + m⟩

@[simp]
theorem fiberPoint_x1 (c u t q h : K) :
    (fiberPoint c u t q h).x1 = u :=
  rfl

/-- The affine half-step multiplies the torus parameter by `q`. -/
theorem affineStep_fiberPoint_movingCoordinates
    (c u t q h : K) (hq : q ≠ 0) (hh : h ≠ 0)
    (htrace : t = q + q⁻¹) (ht : t ≠ 2) :
    affineStep c u t
        ((fiberPoint c u t q h).x2, (fiberPoint c u t q h).x3) =
      ((fiberPoint c u t q (q * h)).x2,
        (fiberPoint c u t q (q * h)).x3) := by
  apply centerCoordinates_injective (fiberCenter c u t)
  rw [centerCoordinates_affineStep c u t _ ht]
  simpa [fiberPoint, centerCoordinates] using
    linearStep_torusPair t q (centeredFiberProduct c u t) h hq hh htrace

/-- The actual project rotation, which is the square of the half-step,
multiplies the torus parameter by `q²`. -/
theorem affineStep_sq_fiberPoint_movingCoordinates
    (c u t q h : K) (hq : q ≠ 0) (hh : h ≠ 0)
    (htrace : t = q + q⁻¹) (ht : t ≠ 2) :
    affineStep c u t (affineStep c u t
        ((fiberPoint c u t q h).x2, (fiberPoint c u t q h).x3)) =
      ((fiberPoint c u t q (q ^ 2 * h)).x2,
        (fiberPoint c u t q (q ^ 2 * h)).x3) := by
  rw [affineStep_fiberPoint_movingCoordinates c u t q h hq hh htrace ht]
  rw [affineStep_fiberPoint_movingCoordinates c u t q (q * h) hq
    (mul_ne_zero hq hh) htrace ht]
  rw [show q * (q * h) = q ^ 2 * h by ring]

/-- The parametrized point lies on the symmetric surface. -/
theorem fiberPoint_isSolution
    (c u t q h : K) (hq : q ≠ 0) (hh : h ≠ 0)
    (htraceEigenvalue : t = q + q⁻¹)
    (htraceCoordinate : t = trace c u)
    (hD : discriminant t ≠ 0) :
    IsSolution (coefficients c) (fiberPoint c u t q h) := by
  have ht : t ≠ 2 := ne_two_of_discriminant_ne_zero hD
  have hD' : t ^ 2 - 4 ≠ 0 := by
    simpa only [discriminant] using hD
  rw [IsSolution]
  rw [show fiberPoint c u t q h =
      ⟨u,
        (torusPair q (centeredFiberProduct c u t) h).1 + fiberCenter c u t,
        (torusPair q (centeredFiberProduct c u t) h).2 + fiberCenter c u t⟩ by
      rfl]
  rw [polynomial_centered_fixed_first c u t _ _ htraceCoordinate ht]
  rw [torusPair_conic t q (centeredFiberProduct c u t) h hq hh
    htraceEigenvalue]
  simp only [centeredFiberProduct, discriminant]
  field_simp [hD', sub_ne_zero.mpr ht]
  ring

/-- Exact adjacent-trace formula on the torus parametrization. -/
theorem trace_fiberPoint_x2
    (c u t q h : K) (hh : h ≠ 0) :
    trace c (fiberPoint c u t q h).x2 =
      actualAlpha c * h + actualBeta c u t / h + actualGamma c u t := by
  simp [fiberPoint, torusPair, trace, actualAlpha, actualBeta,
    actualGamma, centeredFiberProduct]
  field_simp [hh]
  ring

/-- The actual weight product is the ordered shifted-cover parameter. -/
theorem actualSigma_eq_orderedTraceSigma
    (c u t : K) (htrace : t = trace c u)
    (hD : discriminant t ≠ 0) :
    actualSigma c u t = orderedTraceSigma c c c t := by
  have htTwo : t ≠ 2 := ne_two_of_discriminant_ne_zero hD
  have hD' : t ^ 2 - 4 ≠ 0 := by
    simpa only [discriminant] using hD
  have hsu : multiplier c * u = t + c := by
    rw [htrace, trace]
    ring
  have hsq : multiplier c ^ 2 * u ^ 2 = (t + c) ^ 2 := by
    rw [← mul_pow, hsu]
  rw [actualSigma, actualAlpha, actualBeta, centeredFiberProduct]
  rw [show multiplier c * (multiplier c *
      (u ^ 2 * (t + c ^ 2 - 2) / ((t - 2) * discriminant t))) =
      (multiplier c ^ 2 * u ^ 2) * (t + c ^ 2 - 2) /
        ((t - 2) * discriminant t) by ring]
  rw [hsq]
  simp only [orderedTraceSigma, discriminant]
  field_simp [hD', sub_ne_zero.mpr htTwo]
  ring

/-- Closed form of the actual affine shift. -/
theorem actualGamma_symmetric
    (c u t : K) (htrace : t = trace c u)
    (htTwo : t ≠ 2) :
    actualGamma c u t = c * (c + 2) / (t - 2) := by
  have hsu : multiplier c * u = t + c := by
    rw [htrace, trace]
    ring
  rw [actualGamma, fiberCenter]
  rw [show multiplier c * (c * u / (t - 2)) - c =
      c * (multiplier c * u) / (t - 2) - c by ring]
  rw [hsu]
  field_simp [sub_ne_zero.mpr htTwo]
  ring

/-- Closed form of the symmetric affine shift. -/
theorem orderedTraceGamma_symmetric
    (c t : K) (hD : discriminant t ≠ 0) :
    orderedTraceGamma c c c t = c * (c + 2) / (t - 2) := by
  have htTwo : t ≠ 2 := ne_two_of_discriminant_ne_zero hD
  have hD' : t ^ 2 - 4 ≠ 0 := by
    simpa only [discriminant] using hD
  simp only [orderedTraceGamma, eval_orderedTraceShiftPolynomial]
  field_simp [hD', sub_ne_zero.mpr htTwo]
  ring

/-- The actual affine trace shift is the ordered shifted-cover parameter. -/
theorem actualGamma_eq_orderedTraceGamma
    (c u t : K) (htrace : t = trace c u)
    (hD : discriminant t ≠ 0) :
    actualGamma c u t = orderedTraceGamma c c c t := by
  rw [actualGamma_symmetric c u t htrace
    (ne_two_of_discriminant_ne_zero hD)]
  exact (orderedTraceGamma_symmetric c t hD).symm

/-- In the classical subfamily `c=0`, the normalized weight is `t²/D`. -/
theorem orderedTraceSigma_zero
    (t : K) (hD : discriminant t ≠ 0) :
    orderedTraceSigma 0 0 0 t = t ^ 2 / discriminant t := by
  have hD' : t ^ 2 - 4 ≠ 0 := by
    simpa only [discriminant] using hD
  simp only [orderedTraceSigma, discriminant]
  field_simp [hD']
  ring

/-- Under the symmetric coefficient hypothesis, a nonparabolic ordered trace
never lies on the toric-component locus `(sigma,gamma)=(1,0)`. -/
theorem orderedTrace_not_toric
    (c t : K) (htwo : (2 : K) ≠ 0) (hc : c ^ 2 ≠ 4)
    (hD : discriminant t ≠ 0) :
    ¬(orderedTraceSigma c c c t = 1 ∧
      orderedTraceGamma c c c t = 0) := by
  rintro ⟨hsigma, hgamma⟩
  by_cases hcZero : c = 0
  · subst c
    rw [orderedTraceSigma_zero t hD] at hsigma
    have hfour : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 ^ 2 by norm_num]
      exact pow_ne_zero 2 htwo
    simp only [discriminant] at hsigma hD
    field_simp [hD] at hsigma
    apply hfour
    linear_combination hsigma
  · have hcPlusTwo : c + 2 ≠ 0 := by
      intro h
      apply hc
      have hcEq : c = -2 := eq_neg_of_add_eq_zero_left h
      rw [hcEq]
      norm_num
    rw [orderedTraceGamma_symmetric c t hD] at hgamma
    exact (div_ne_zero (mul_ne_zero hcZero hcPlusTwo) (by
      intro ht
      exact (ne_two_of_discriminant_ne_zero hD) (sub_eq_zero.mp ht))).elim hgamma

/-- The first common-even factor becomes a constant in the symmetric family. -/
theorem eval_orderedTraceEvenMinusPolynomial_symmetric (c t : K) :
    Polynomial.eval t (orderedTraceEvenMinusPolynomial c c c) =
      (4 - c ^ 2) * (c - 2) := by
  rw [eval_orderedTraceEvenMinusPolynomial]
  ring

/-- The remaining common-even factor is one explicit affine function. -/
theorem eval_orderedTraceEvenPlusPolynomial_symmetric (c t : K) :
    Polynomial.eval t (orderedTraceEvenPlusPolynomial c c c) =
      8 * c * t - c ^ 3 + 6 * c ^ 2 + 4 * c + 8 := by
  rw [eval_orderedTraceEvenPlusPolynomial]
  ring

/-- The constant common-even factor cannot vanish when `c² ≠ 4`. -/
theorem eval_orderedTraceEvenMinusPolynomial_symmetric_ne_zero
    (c t : K) (hc : c ^ 2 ≠ 4) :
    Polynomial.eval t (orderedTraceEvenMinusPolynomial c c c) ≠ 0 := by
  rw [eval_orderedTraceEvenMinusPolynomial_symmetric]
  apply mul_ne_zero
  · exact sub_ne_zero.mpr hc.symm
  · intro hcTwo
    apply hc
    rw [sub_eq_zero.mp hcTwo]
    norm_num

end

end GenMarkoff.Symmetric
