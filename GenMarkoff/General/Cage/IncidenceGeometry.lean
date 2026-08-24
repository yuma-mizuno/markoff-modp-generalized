import GenMarkoff.General.TraceSurface
import GenMarkoff.TraceCurve.ExceptionalRouting
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Coefficient-ordered incidence geometry for the unequal trace surface

Fix a first-axis trace `xi` and a second-axis trace `middle`.  The unequal
trace surface is a monic quadratic in the third trace with linear coefficient

`traceLinearCoefficient3 a - xi * middle`.

The corresponding discriminant is again quadratic in `middle`, but its
scalar discriminant is now the ordered factor

`16 * (xi + a.a1)^2 * centeredNorm a.a2 a.a3 xi`.

This replaces the symmetric factorization and is a genuinely new cage
calculation.  The factorization exactly matches the first three
candidate-regular conditions in the frame `(a₁,a₂,a₃)`.  This file develops
only the algebraic incidence interface; it does not claim the parity-aware
point count needed to connect actual `q²` rotation cycles.
-/

namespace GenMarkoff.General.Cage

open Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- A trace-coordinate point with prescribed first and second traces. -/
def incidenceTracePoint (xi middle z : K) : Point K :=
  ⟨xi, middle, z⟩

omit [Field K] in
@[simp]
theorem incidenceTracePoint_x1 (xi middle z : K) :
    (incidenceTracePoint xi middle z).x1 = xi :=
  rfl

omit [Field K] in
@[simp]
theorem incidenceTracePoint_x2 (xi middle z : K) :
    (incidenceTracePoint xi middle z).x2 = middle :=
  rfl

omit [Field K] in
@[simp]
theorem incidenceTracePoint_x3 (xi middle z : K) :
    (incidenceTracePoint xi middle z).x3 = z :=
  rfl

/-- Discriminant in the third trace after fixing the first two traces. -/
def incidenceDiscriminant
    (a : Coefficients K) (xi middle : K) : K :=
  (traceLinearCoefficient3 a - xi * middle) ^ 2 -
    4 * (xi ^ 2 + middle ^ 2 +
      traceLinearCoefficient1 a * xi +
      traceLinearCoefficient2 a * middle +
      traceConstant a)

/-- The same incidence discriminant as a polynomial in the middle trace. -/
def incidenceDiscriminantPolynomial
    (a : Coefficients K) (xi : K) : K[X] :=
  (C (traceLinearCoefficient3 a) - C xi * X) ^ 2 -
    4 * (C (xi ^ 2) + X ^ 2 +
      C (traceLinearCoefficient1 a * xi) +
      C (traceLinearCoefficient2 a) * X +
      C (traceConstant a))

@[simp]
theorem eval_incidenceDiscriminantPolynomial
    (a : Coefficients K) (xi middle : K) :
    eval middle (incidenceDiscriminantPolynomial a xi) =
      incidenceDiscriminant a xi middle := by
  simp [incidenceDiscriminantPolynomial, incidenceDiscriminant]

/-- Leading coefficient of the incidence discriminant as a quadratic in
the middle trace. -/
def incidenceLeadingCoefficient (xi : K) : K :=
  xi ^ 2 - 4

/-- Linear coefficient of the incidence discriminant as a quadratic in the
middle trace. -/
def incidenceLinearCoefficient
    (a : Coefficients K) (xi : K) : K :=
  -2 * traceLinearCoefficient3 a * xi -
    4 * traceLinearCoefficient2 a

/-- Constant coefficient of the incidence discriminant as a quadratic in
the middle trace. -/
def incidenceConstantCoefficient
    (a : Coefficients K) (xi : K) : K :=
  traceLinearCoefficient3 a ^ 2 -
    4 * xi ^ 2 -
    4 * traceLinearCoefficient1 a * xi -
    4 * traceConstant a

/-- Expanded quadratic form of the incidence discriminant polynomial. -/
theorem incidenceDiscriminantPolynomial_eq_quadratic
    (a : Coefficients K) (xi : K) :
    incidenceDiscriminantPolynomial a xi =
      C (incidenceLeadingCoefficient xi) * X ^ 2 +
        C (incidenceLinearCoefficient a xi) * X +
          C (incidenceConstantCoefficient a xi) := by
  simp only [incidenceDiscriminantPolynomial, incidenceLeadingCoefficient,
    incidenceLinearCoefficient, incidenceConstantCoefficient]
  simp only [map_sub, map_neg, map_mul, map_pow, map_ofNat]
  ring

/-- Scalar discriminant of the quadratic incidence polynomial. -/
def incidenceQuadraticDiscriminant
    (a : Coefficients K) (xi : K) : K :=
  incidenceLinearCoefficient a xi ^ 2 -
    4 * incidenceLeadingCoefficient xi *
      incidenceConstantCoefficient a xi

/-- Exact ordered factorization of the scalar discriminant. -/
theorem incidenceQuadraticDiscriminant_factor
    (a : Coefficients K) (xi : K) :
    incidenceQuadraticDiscriminant a xi =
      16 * (xi + a.a1) ^ 2 *
        centeredNorm a.a2 a.a3 xi := by
  simp only [incidenceQuadraticDiscriminant,
    incidenceLinearCoefficient, incidenceLeadingCoefficient,
    incidenceConstantCoefficient, traceLinearCoefficient1,
    traceLinearCoefficient2, traceLinearCoefficient3, traceConstant,
    centeredNorm, discriminant]
  ring

/-- Candidate regularity in the ordered first-axis frame makes the
incidence quadratic separable. -/
theorem incidenceQuadraticDiscriminant_ne_zero_of_candidateRegular
    (a : Coefficients K) (xi : K)
    (h2 : (2 : K) ≠ 0)
    (hregular :
      OrderedTraceCandidateRegular a.a1 a.a2 a.a3 xi) :
    incidenceQuadraticDiscriminant a xi ≠ 0 := by
  have hxiA : xi + a.a1 ≠ 0 := hregular.2.1
  have hcenter : centeredNorm a.a2 a.a3 xi ≠ 0 := by
    simpa only [eval_orderedTraceCenteredNormPolynomial,
      centeredNorm, discriminant] using hregular.2.2.1
  have hsixteen : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 2 * 2 * (2 * 2) by norm_num]
    exact mul_ne_zero (mul_ne_zero h2 h2) (mul_ne_zero h2 h2)
  rw [incidenceQuadraticDiscriminant_factor]
  exact mul_ne_zero
    (mul_ne_zero hsixteen (pow_ne_zero 2 hxiA)) hcenter

/-- The trace-surface equation as a monic quadratic in the third trace. -/
theorem tracePolynomial_incidenceTracePoint_eq_quadratic
    (a : Coefficients K) (xi middle z : K) :
    tracePolynomial a (incidenceTracePoint xi middle z) =
      z ^ 2 +
        (traceLinearCoefficient3 a - xi * middle) * z +
        (xi ^ 2 + middle ^ 2 +
          traceLinearCoefficient1 a * xi +
          traceLinearCoefficient2 a * middle +
          traceConstant a) := by
  simp only [tracePolynomial, incidenceTracePoint]
  ring

/-- Division-free completion of the third-trace square. -/
theorem incidence_square_sub_discriminant
    (a : Coefficients K) (xi middle z : K) :
    (2 * z + (traceLinearCoefficient3 a - xi * middle)) ^ 2 -
        incidenceDiscriminant a xi middle =
      4 * tracePolynomial a (incidenceTracePoint xi middle z) := by
  rw [tracePolynomial_incidenceTracePoint_eq_quadratic]
  simp only [incidenceDiscriminant]
  ring

/-- Recover the trace-surface point from a square root of the ordered
incidence discriminant. -/
def incidenceRootPoint
    (a : Coefficients K) (xi middle root : K) : Point K :=
  incidenceTracePoint xi middle
    ((root -
      (traceLinearCoefficient3 a - xi * middle)) / 2)

@[simp]
theorem incidenceRootPoint_x1
    (a : Coefficients K) (xi middle root : K) :
    (incidenceRootPoint a xi middle root).x1 = xi :=
  rfl

@[simp]
theorem incidenceRootPoint_x2
    (a : Coefficients K) (xi middle root : K) :
    (incidenceRootPoint a xi middle root).x2 = middle :=
  rfl

/-- A discriminant square root gives an actual point of the unequal trace
surface. -/
theorem tracePolynomial_incidenceRootPoint_eq_zero
    (a : Coefficients K) (xi middle root : K)
    (h2 : (2 : K) ≠ 0)
    (hroot : root ^ 2 = incidenceDiscriminant a xi middle) :
    tracePolynomial a (incidenceRootPoint a xi middle root) = 0 := by
  have hfour : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  apply (mul_eq_zero_iff_left hfour).mp
  change
    4 * tracePolynomial a
      (incidenceTracePoint xi middle
        ((root -
          (traceLinearCoefficient3 a - xi * middle)) / 2)) = 0
  rw [← incidence_square_sub_discriminant]
  have hlinear :
      2 *
          ((root -
            (traceLinearCoefficient3 a - xi * middle)) / 2) +
          (traceLinearCoefficient3 a - xi * middle) =
        root := by
    field_simp [h2]
    ring
  rw [hlinear, hroot]
  simp

/-- Conversely, a trace-surface point supplies its canonical discriminant
square root. -/
theorem incidenceDiscriminant_eq_square_of_tracePolynomial_eq_zero
    (a : Coefficients K) (xi middle z : K)
    (hz : tracePolynomial a (incidenceTracePoint xi middle z) = 0) :
    incidenceDiscriminant a xi middle =
      (2 * z +
        (traceLinearCoefficient3 a - xi * middle)) ^ 2 := by
  have hcompletion :=
    incidence_square_sub_discriminant a xi middle z
  rw [hz, mul_zero] at hcompletion
  exact (sub_eq_zero.mp hcompletion).symm

/-- A concrete pair of trace-surface points with different prescribed
first traces and one shared second trace. -/
structure IncidenceEquationWitness
    (a : Coefficients K) (xi eta : K) where
  middle : K
  firstRoot : K
  secondRoot : K
  firstEquation :
    firstRoot ^ 2 = incidenceDiscriminant a xi middle
  secondEquation :
    secondRoot ^ 2 = incidenceDiscriminant a eta middle

/-- First trace-surface point represented by an incidence witness. -/
def IncidenceEquationWitness.firstTracePoint
    {a : Coefficients K} {xi eta : K}
    (w : IncidenceEquationWitness a xi eta) : Point K :=
  incidenceRootPoint a xi w.middle w.firstRoot

/-- Second trace-surface point represented by an incidence witness. -/
def IncidenceEquationWitness.secondTracePoint
    {a : Coefficients K} {xi eta : K}
    (w : IncidenceEquationWitness a xi eta) : Point K :=
  incidenceRootPoint a eta w.middle w.secondRoot

@[simp]
theorem IncidenceEquationWitness.firstTracePoint_x1
    {a : Coefficients K} {xi eta : K}
    (w : IncidenceEquationWitness a xi eta) :
    w.firstTracePoint.x1 = xi :=
  rfl

@[simp]
theorem IncidenceEquationWitness.secondTracePoint_x1
    {a : Coefficients K} {xi eta : K}
    (w : IncidenceEquationWitness a xi eta) :
    w.secondTracePoint.x1 = eta :=
  rfl

@[simp]
theorem IncidenceEquationWitness.firstTracePoint_x2
    {a : Coefficients K} {xi eta : K}
    (w : IncidenceEquationWitness a xi eta) :
    w.firstTracePoint.x2 = w.middle :=
  rfl

@[simp]
theorem IncidenceEquationWitness.secondTracePoint_x2
    {a : Coefficients K} {xi eta : K}
    (w : IncidenceEquationWitness a xi eta) :
    w.secondTracePoint.x2 = w.middle :=
  rfl

theorem IncidenceEquationWitness.firstTracePoint_mem
    {a : Coefficients K} {xi eta : K}
    (w : IncidenceEquationWitness a xi eta)
    (h2 : (2 : K) ≠ 0) :
    tracePolynomial a w.firstTracePoint = 0 :=
  tracePolynomial_incidenceRootPoint_eq_zero
    a xi w.middle w.firstRoot h2 w.firstEquation

theorem IncidenceEquationWitness.secondTracePoint_mem
    {a : Coefficients K} {xi eta : K}
    (w : IncidenceEquationWitness a xi eta)
    (h2 : (2 : K) ≠ 0) :
    tracePolynomial a w.secondTracePoint = 0 :=
  tracePolynomial_incidenceRootPoint_eq_zero
    a eta w.middle w.secondRoot h2 w.secondEquation

/-- Pull the first trace witness back to the original fixed-coefficient
surface. -/
theorem IncidenceEquationWitness.firstPoint_isSolution
    {a : Coefficients K} {xi eta : K}
    (w : IncidenceEquationWitness a xi eta)
    (h2 : (2 : K) ≠ 0)
    (hs : a.multiplier ≠ 0) :
    IsSolution a (inverseTracePoint a w.firstTracePoint) :=
  isSolution_inverseTracePoint a w.firstTracePoint hs
    (w.firstTracePoint_mem h2)

/-- Pull the second trace witness back to the original fixed-coefficient
surface. -/
theorem IncidenceEquationWitness.secondPoint_isSolution
    {a : Coefficients K} {xi eta : K}
    (w : IncidenceEquationWitness a xi eta)
    (h2 : (2 : K) ≠ 0)
    (hs : a.multiplier ≠ 0) :
    IsSolution a (inverseTracePoint a w.secondTracePoint) :=
  isSolution_inverseTracePoint a w.secondTracePoint hs
    (w.secondTracePoint_mem h2)

end

end GenMarkoff.General.Cage
