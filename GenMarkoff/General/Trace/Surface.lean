import GenMarkoff.General.Axis

/-!
# The generalized surface in trace coordinates

The affine trace change (`tracePoint`)

`tᵢ = a.multiplier * xᵢ - aᵢ`

sends the generalized surface to the cubic `tracePolynomial a`,
`t₁² + t₂² + t₃² - t₁t₂t₃ + c₁t₁ + c₂t₂ + c₃t₃ + d`, with linear coefficients

`2 * a₁ + a₂ * a₃`, `2 * a₂ + a₃ * a₁`, and
`2 * a₃ + a₁ * a₂`

and constant `d = a₁² + a₂² + a₃² + 2a₁a₂a₃`.  Unlike the classical Markoff
case these terms do not vanish in general, so they are kept explicit.  The
file proves the division-free identity
`tracePolynomial a (tracePoint a x) = s² * polynomial a x` and, for `s ≠ 0`,
inverts the trace change.  No coordinate permutation is used.
-/

namespace GenMarkoff.General

universe u

/-- The linear coefficient of the first trace coordinate. -/
def traceLinearCoefficient1 {R : Type u} [CommRing R]
    (a : Coefficients R) : R :=
  2 * a.a1 + a.a2 * a.a3

/-- The linear coefficient of the second trace coordinate. -/
def traceLinearCoefficient2 {R : Type u} [CommRing R]
    (a : Coefficients R) : R :=
  2 * a.a2 + a.a3 * a.a1

/-- The linear coefficient of the third trace coordinate. -/
def traceLinearCoefficient3 {R : Type u} [CommRing R]
    (a : Coefficients R) : R :=
  2 * a.a3 + a.a1 * a.a2

/-- The constant coefficient of the trace cubic. -/
def traceConstant {R : Type u} [CommRing R]
    (a : Coefficients R) : R :=
  a.a1 ^ 2 + a.a2 ^ 2 + a.a3 ^ 2 +
    2 * a.a1 * a.a2 * a.a3

/-- The coefficient-ordered affine trace cubic. -/
def tracePolynomial {R : Type u} [CommRing R]
    (a : Coefficients R) (t : Point R) : R :=
  t.x1 ^ 2 + t.x2 ^ 2 + t.x3 ^ 2 -
      t.x1 * t.x2 * t.x3 +
    traceLinearCoefficient1 a * t.x1 +
    traceLinearCoefficient2 a * t.x2 +
    traceLinearCoefficient3 a * t.x3 +
    traceConstant a

/-- Apply the fixed-coefficient affine trace change in all three
coordinates. -/
def tracePoint {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) : Point R :=
  ⟨orderedTrace a.multiplier a.a1 x.x1,
    orderedTrace a.multiplier a.a2 x.x2,
    orderedTrace a.multiplier a.a3 x.x3⟩

@[simp]
theorem tracePoint_x1 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    (tracePoint a x).x1 = orderedTrace a.multiplier a.a1 x.x1 :=
  rfl

@[simp]
theorem tracePoint_x2 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    (tracePoint a x).x2 = orderedTrace a.multiplier a.a2 x.x2 :=
  rfl

@[simp]
theorem tracePoint_x3 {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    (tracePoint a x).x3 = orderedTrace a.multiplier a.a3 x.x3 :=
  rfl

/-- Division-free trace normalization: the trace cubic at the trace point is
`s²` times the generalized Markoff polynomial. -/
theorem tracePolynomial_tracePoint
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    tracePolynomial a (tracePoint a x) =
      a.multiplier ^ 2 * polynomial a x := by
  simp [tracePolynomial, tracePoint, traceLinearCoefficient1,
    traceLinearCoefficient2, traceLinearCoefficient3, traceConstant,
    orderedTrace, polynomial, Coefficients.multiplier]
  ring

/-- When the multiplier is nonzero, a point lies on the generalized surface
exactly when its trace point lies on the trace cubic. -/
theorem isSolution_iff_tracePolynomial_tracePoint
    {K : Type u} [Field K]
    (a : Coefficients K) (x : Point K)
    (hs : a.multiplier ≠ 0) :
    IsSolution a x ↔ tracePolynomial a (tracePoint a x) = 0 := by
  rw [IsSolution, tracePolynomial_tracePoint]
  exact (mul_eq_zero_iff_left (pow_ne_zero 2 hs)).symm

/-- Inverse of one coefficient-ordered affine trace coordinate. -/
def inverseTraceCoordinate {K : Type u} [Field K]
    (s A t : K) : K :=
  (t + A) / s

/-- Coordinatewise inverse of the affine trace change, valid when the
multiplier is nonzero. -/
def inverseTracePoint {K : Type u} [Field K]
    (a : Coefficients K) (t : Point K) : Point K :=
  ⟨inverseTraceCoordinate a.multiplier a.a1 t.x1,
    inverseTraceCoordinate a.multiplier a.a2 t.x2,
    inverseTraceCoordinate a.multiplier a.a3 t.x3⟩

@[simp]
theorem orderedTrace_inverseTraceCoordinate
    {K : Type u} [Field K]
    (s A t : K) (hs : s ≠ 0) :
    orderedTrace s A (inverseTraceCoordinate s A t) = t := by
  simp only [orderedTrace, inverseTraceCoordinate]
  field_simp [hs]
  ring

@[simp]
theorem tracePoint_inverseTracePoint
    {K : Type u} [Field K]
    (a : Coefficients K) (t : Point K)
    (hs : a.multiplier ≠ 0) :
    tracePoint a (inverseTracePoint a t) = t := by
  ext <;>
    simp [tracePoint, inverseTracePoint,
      orderedTrace_inverseTraceCoordinate _ _ _ hs]

@[simp]
theorem inverseTracePoint_tracePoint
    {K : Type u} [Field K]
    (a : Coefficients K) (x : Point K)
    (hs : a.multiplier ≠ 0) :
    inverseTracePoint a (tracePoint a x) = x := by
  ext <;>
    simp [tracePoint, inverseTracePoint, inverseTraceCoordinate,
      orderedTrace]
  all_goals field_simp [hs]

/-- When the multiplier is nonzero, a point of the trace cubic pulls back to
the generalized surface. -/
theorem isSolution_inverseTracePoint
    {K : Type u} [Field K]
    (a : Coefficients K) (t : Point K)
    (hs : a.multiplier ≠ 0)
    (ht : tracePolynomial a t = 0) :
    IsSolution a (inverseTracePoint a t) := by
  rw [isSolution_iff_tracePolynomial_tracePoint a _ hs]
  simpa [tracePoint_inverseTracePoint a t hs] using ht

end GenMarkoff.General
