import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Incidence discriminants for the symmetric generalized Markoff surface

In symmetric trace coordinates the surface has the form

`x² + y² + z² - xyz + A (x + y + z) + B = 0`,

where `A = c(c+2)` and `B = c²(2c+3)`.  Fixing the trace `ξ` and viewing
the equation as a quadratic in one of the remaining coordinates gives the
incidence discriminant

`Δ_{c,ξ}(T) = (A-ξT)² - 4(ξ²+T²+A(ξ+T)+B)`.

This file records two exact algebraic identities needed by a future cage
argument:

* the quadratic discriminant of `Δ_{c,ξ}` factors into four explicit
  exceptional factors;
* the formal-degree-two resultant of `Δ_{c,ξ}` and `Δ_{c,η}` factors as
  the diagonal square times a single symmetric obstruction `R_c(ξ,η)`.

These are polynomial identities over an arbitrary commutative ring.  No
geometric smoothness or point-counting claim is made here.
-/

namespace GenMarkoff.Symmetric.Cage

open Polynomial

noncomputable section

variable {K : Type*} [CommRing K]

/-- The linear trace coefficient `A = c(c+2)` of the symmetric surface. -/
def traceSurfaceA (c : K) : K :=
  c * (c + 2)

/-- The constant trace coefficient `B = c²(2c+3)` of the symmetric surface. -/
def traceSurfaceB (c : K) : K :=
  c ^ 2 * (2 * c + 3)

/-- The incidence discriminant after fixing one trace `ξ`. -/
def incidenceDiscriminant (c ξ T : K) : K :=
  (traceSurfaceA c - ξ * T) ^ 2 -
    4 * (ξ ^ 2 + T ^ 2 + traceSurfaceA c * (ξ + T) + traceSurfaceB c)

/-- The incidence discriminant as a polynomial in the remaining trace. -/
def incidenceDiscriminantPolynomial (c ξ : K) : K[X] :=
  (C (traceSurfaceA c) - C ξ * X) ^ 2 -
    4 * (C (ξ ^ 2) + X ^ 2 +
      C (traceSurfaceA c) * (C ξ + X) + C (traceSurfaceB c))

@[simp]
theorem eval_incidenceDiscriminantPolynomial (c ξ T : K) :
    eval T (incidenceDiscriminantPolynomial c ξ) =
      incidenceDiscriminant c ξ T := by
  simp [incidenceDiscriminantPolynomial, incidenceDiscriminant]

/-- The leading coefficient of `Δ_{c,ξ}` as a quadratic in `T`. -/
def incidenceLeadingCoefficient (ξ : K) : K :=
  ξ ^ 2 - 4

/-- The linear coefficient of `Δ_{c,ξ}` as a quadratic in `T`. -/
def incidenceLinearCoefficient (c ξ : K) : K :=
  -2 * traceSurfaceA c * (ξ + 2)

/-- The constant coefficient of `Δ_{c,ξ}` as a quadratic in `T`. -/
def incidenceConstantCoefficient (c ξ : K) : K :=
  traceSurfaceA c ^ 2 - 4 * ξ ^ 2 -
    4 * traceSurfaceA c * ξ - 4 * traceSurfaceB c

/-- Expanded quadratic form of the incidence discriminant polynomial. -/
theorem incidenceDiscriminantPolynomial_eq_quadratic (c ξ : K) :
    incidenceDiscriminantPolynomial c ξ =
      C (incidenceLeadingCoefficient ξ) * X ^ 2 +
        C (incidenceLinearCoefficient c ξ) * X +
          C (incidenceConstantCoefficient c ξ) := by
  simp only [incidenceDiscriminantPolynomial, incidenceLeadingCoefficient,
    incidenceLinearCoefficient, incidenceConstantCoefficient]
  simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]
  ring

/-- The ordinary scalar discriminant of the quadratic `Δ_{c,ξ}`. -/
def incidenceQuadraticDiscriminant (c ξ : K) : K :=
  incidenceLinearCoefficient c ξ ^ 2 -
    4 * incidenceLeadingCoefficient ξ * incidenceConstantCoefficient c ξ

/-- Exact factorization of the quadratic discriminant of `Δ_{c,ξ}`. -/
theorem incidenceQuadraticDiscriminant_factor (c ξ : K) :
    incidenceQuadraticDiscriminant c ξ =
      16 * (ξ + 2) * (ξ + c) ^ 2 * (ξ + c ^ 2 - 2) := by
  simp only [incidenceQuadraticDiscriminant, incidenceLinearCoefficient,
    incidenceLeadingCoefficient, incidenceConstantCoefficient,
    traceSurfaceA, traceSurfaceB]
  ring

/-- Closed formula for the formal-degree-two resultant of two quadratics.

The explicit formal degrees matter: this identity remains valid when a
displayed leading coefficient specializes to zero. -/
theorem resultant_quadratic_quadratic
    (a b d e f h : K) :
    Polynomial.resultant
        (C a * X ^ 2 + C b * X + C d)
        (C e * X ^ 2 + C f * X + C h) 2 2 =
      (a * h - d * e) ^ 2 -
        (a * f - b * e) * (b * h - d * f) := by
  rw [Polynomial.resultant]
  let M : Matrix (Fin 4) (Fin 4) K :=
    !![h, 0, d, 0;
       f, h, b, d;
       e, f, a, b;
       0, e, 0, a]
  have hsyl :
      Polynomial.sylvester
          (C a * X ^ 2 + C b * X + C d)
          (C e * X ^ 2 + C f * X + C h) 2 2 =
        M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.sylvester, Fin.addCases, Fin.castAdd, Fin.natAdd,
        Polynomial.coeff_X, M]
  have hM00 : M 0 0 = h := by rfl
  have hM01 : M 0 1 = 0 := by rfl
  have hM02 : M 0 2 = d := by rfl
  have hM03 : M 0 3 = 0 := by rfl
  have hsub0 :
      M.submatrix Fin.succ Fin.succ =
        !![h, b, d;
           f, a, b;
           e, 0, a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hsub2 :
      M.submatrix Fin.succ (Fin.succAbove (2 : Fin 4)) =
        !![f, h, d;
           e, f, b;
           0, e, a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hsyl, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  rw [hM00, hM01, hM02, hM03]
  norm_num [Fin.succAbove_zero]
  rw [hsub0, hsub2]
  simp [Matrix.det_fin_three]
  ring

/-- The symmetric off-diagonal obstruction in the pair resultant.

Here `s = ξ+η` and `r = ξη`; the displayed form makes symmetry in `ξ,η`
manifest. -/
def incidencePairObstruction (c ξ η : K) : K :=
  let s := ξ + η
  let r := ξ * η
  (-c ^ 3 + 6 * c ^ 2 + 4 * c + 8) * s ^ 2 +
    8 * c * r * s +
    4 * c ^ 2 * (c + 2) * r +
    8 * c * (c ^ 2 + 2 * c + 4) * s +
    16 * c ^ 2 * (c + 2)

/-- `R_c(ξ,η)` is symmetric in its two trace arguments. -/
theorem incidencePairObstruction_comm (c ξ η : K) :
    incidencePairObstruction c ξ η =
      incidencePairObstruction c η ξ := by
  simp only [incidencePairObstruction]
  ring

/-- The pair resultant, with both incidence polynomials assigned formal
degree two. -/
def incidencePairResultant (c ξ η : K) : K :=
  Polynomial.resultant
    (incidenceDiscriminantPolynomial c ξ)
    (incidenceDiscriminantPolynomial c η) 2 2

/-- Exact factorization of the pair resultant.

The factor `(η-ξ)²` is the diagonal.  The coefficient specializations
`c = ±2` are kept visible rather than cancelled, and the remaining factor
is `R_c(ξ,η)`. -/
theorem incidencePairResultant_factor (c ξ η : K) :
    incidencePairResultant c ξ η =
      -(η - ξ) ^ 2 * (c + 2) ^ 2 * (c - 2) ^ 3 *
        incidencePairObstruction c ξ η := by
  rw [incidencePairResultant,
    incidenceDiscriminantPolynomial_eq_quadratic c ξ,
    incidenceDiscriminantPolynomial_eq_quadratic c η,
    resultant_quadratic_quadratic]
  simp only [incidenceLeadingCoefficient, incidenceLinearCoefficient,
    incidenceConstantCoefficient, traceSurfaceA, traceSurfaceB,
    incidencePairObstruction]
  ring

end

end GenMarkoff.Symmetric.Cage
