import GenMarkoff.General.Axis

/-!
# The unequal-coefficient surface in trace coordinates

The affine trace change

`tᵢ = a.multiplier * xᵢ - aᵢ`

does not send a fixed unequal-coefficient surface to the symmetric trace
cubic.  Instead the three linear coefficients are

`2 * a₁ + a₂ * a₃`, `2 * a₂ + a₃ * a₁`, and
`2 * a₃ + a₁ * a₂`.

This asymmetry is a genuinely new cage consideration.  We keep the three
terms explicit and prove the division-free normalization identity, together
with the coefficient-ordered trace versions of the three Vieta moves.  No
coordinate permutation is used.
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

/-- The constant coefficient of the unequal trace cubic. -/
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

/-- Division-free normalization of the fixed unequal-coefficient surface. -/
theorem tracePolynomial_tracePoint
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    tracePolynomial a (tracePoint a x) =
      a.multiplier ^ 2 * polynomial a x := by
  simp [tracePolynomial, tracePoint, traceLinearCoefficient1,
    traceLinearCoefficient2, traceLinearCoefficient3, traceConstant,
    orderedTrace, polynomial, Coefficients.multiplier]
  ring

/-- Away from the vanishing multiplier, the affine trace change identifies
the original surface with the unequal trace cubic. -/
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

/-- Coordinatewise inverse of the fixed unequal-coefficient trace change. -/
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

/-- A point of the unequal trace cubic pulls back to the original fixed
surface. -/
theorem isSolution_inverseTracePoint
    {K : Type u} [Field K]
    (a : Coefficients K) (t : Point K)
    (hs : a.multiplier ≠ 0)
    (ht : tracePolynomial a t = 0) :
    IsSolution a (inverseTracePoint a t) := by
  rw [isSolution_iff_tracePolynomial_tracePoint a _ hs]
  simpa [tracePoint_inverseTracePoint a t hs] using ht

/-- First Vieta move in coefficient-ordered trace coordinates. -/
def traceVieta1 {R : Type u} [CommRing R]
    (a : Coefficients R) (t : Point R) : Point R :=
  ⟨t.x2 * t.x3 - t.x1 - traceLinearCoefficient1 a, t.x2, t.x3⟩

/-- Second Vieta move in coefficient-ordered trace coordinates. -/
def traceVieta2 {R : Type u} [CommRing R]
    (a : Coefficients R) (t : Point R) : Point R :=
  ⟨t.x1, t.x3 * t.x1 - t.x2 - traceLinearCoefficient2 a, t.x3⟩

/-- Third Vieta move in coefficient-ordered trace coordinates. -/
def traceVieta3 {R : Type u} [CommRing R]
    (a : Coefficients R) (t : Point R) : Point R :=
  ⟨t.x1, t.x2, t.x1 * t.x2 - t.x3 - traceLinearCoefficient3 a⟩

theorem tracePoint_vieta1
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    tracePoint a (vieta1 a x) = traceVieta1 a (tracePoint a x) := by
  ext <;>
    simp [tracePoint, traceVieta1, orderedTrace, vieta1,
      traceLinearCoefficient1, Coefficients.multiplier]
  all_goals ring

theorem tracePoint_vieta2
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    tracePoint a (vieta2 a x) = traceVieta2 a (tracePoint a x) := by
  ext <;>
    simp [tracePoint, traceVieta2, orderedTrace, vieta2,
      traceLinearCoefficient2, Coefficients.multiplier]
  all_goals ring

theorem tracePoint_vieta3
    {R : Type u} [CommRing R]
    (a : Coefficients R) (x : Point R) :
    tracePoint a (vieta3 a x) = traceVieta3 a (tracePoint a x) := by
  ext <;>
    simp [tracePoint, traceVieta3, orderedTrace, vieta3,
      traceLinearCoefficient3, Coefficients.multiplier]
  all_goals ring

/-- The coefficient-ordered trace cubic is preserved by its first Vieta
move. -/
theorem tracePolynomial_traceVieta1
    {R : Type u} [CommRing R]
    (a : Coefficients R) (t : Point R) :
    tracePolynomial a (traceVieta1 a t) = tracePolynomial a t := by
  simp [tracePolynomial, traceVieta1, traceLinearCoefficient1]
  ring

/-- The coefficient-ordered trace cubic is preserved by its second Vieta
move. -/
theorem tracePolynomial_traceVieta2
    {R : Type u} [CommRing R]
    (a : Coefficients R) (t : Point R) :
    tracePolynomial a (traceVieta2 a t) = tracePolynomial a t := by
  simp [tracePolynomial, traceVieta2, traceLinearCoefficient2]
  ring

/-- The coefficient-ordered trace cubic is preserved by its third Vieta
move. -/
theorem tracePolynomial_traceVieta3
    {R : Type u} [CommRing R]
    (a : Coefficients R) (t : Point R) :
    tracePolynomial a (traceVieta3 a t) = tracePolynomial a t := by
  simp [tracePolynomial, traceVieta3, traceLinearCoefficient3]
  ring

end GenMarkoff.General
