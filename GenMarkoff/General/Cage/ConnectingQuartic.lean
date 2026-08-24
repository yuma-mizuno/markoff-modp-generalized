import GenMarkoff.General.Cage.FirstAxisTorusVieta
import GenMarkoff.General.TraceSurface

/-!
# The connecting-fiber quartic for the generalized cluster family

Kingsbury-Neuschotz associates to the first trace-coordinate fiber of

`X^2 + Y^2 + Z^2 = X * Y * Z + A * X + B * Y + C * Z + D`

the quartic

`f₁(X) = X^4 - A * X^3 - (D + 4) * X^2
  + (4 * A + B * C) * X + (4 * D + B^2 + C^2)`.

For the character-surface parameters obtained from the fixed generalized
Markoff coefficient triple, this quartic is not a generic quartic: it factors
as

`(X + a₁)^2 * centeredNorm a₂ a₃ X`.

Thus, away from the already-recorded exceptional value `X = -a₁`, its
quadratic character is exactly that of the existing centered norm.  This is
the first new algebraic input in the full-Vieta connecting-fiber route.
The definitions are coefficient ordered; no coordinate permutation of a
fixed surface is used.
-/

namespace GenMarkoff.General.Cage

universe u

noncomputable section

/-- The quartic controlling whether the two adjacent Vieta involutions act
transitively on a nonparabolic maximal first-coordinate fiber of a character
cubic. -/
def characterConicQuartic
    {R : Type u} [CommRing R] (A B C D X : R) : R :=
  X ^ 4 - A * X ^ 3 - (D + 4) * X ^ 2 +
    (4 * A + B * C) * X + (4 * D + B ^ 2 + C ^ 2)

/-- The defining equation of the character cubic, moved to the left-hand
side. -/
def characterCubicDefect
    {R : Type u} [CommRing R] (A B C D : R) (t : Point R) : R :=
  t.x1 ^ 2 + t.x2 ^ 2 + t.x3 ^ 2 -
    t.x1 * t.x2 * t.x3 -
    A * t.x1 - B * t.x2 - C * t.x3 - D

/-- The trace cubic is exactly the character cubic with the four parameter
signs stated in the source. -/
theorem tracePolynomial_eq_characterCubicDefect
    {R : Type u} [CommRing R] (a : Coefficients R) (t : Point R) :
    tracePolynomial a t =
      characterCubicDefect
        (-traceLinearCoefficient1 a)
        (-traceLinearCoefficient2 a)
        (-traceLinearCoefficient3 a)
        (-traceConstant a) t := by
  simp only [tracePolynomial, characterCubicDefect]
  ring

/-- The first-axis character quartic after substituting the parameters of the
generalized cluster family. -/
def firstAxisConnectingQuartic
    {R : Type u} [CommRing R] (a : Coefficients R) (X : R) : R :=
  characterConicQuartic
    (-traceLinearCoefficient1 a)
    (-traceLinearCoefficient2 a)
    (-traceLinearCoefficient3 a)
    (-traceConstant a) X

/-- Exact specialization of the character-cubic quartic to the generalized
cluster family.  The square factor comes from the triple fixed point
`(-a₁,-a₂,-a₃)` in trace coordinates. -/
theorem firstAxisConnectingQuartic_factor
    {R : Type u} [Field R] (a : Coefficients R) (X : R) :
    firstAxisConnectingQuartic a X =
      (X + a.a1) ^ 2 * centeredNorm a.a2 a.a3 X := by
  simp only [firstAxisConnectingQuartic, characterConicQuartic,
    traceLinearCoefficient1, traceLinearCoefficient2,
    traceLinearCoefficient3, traceConstant, centeredNorm, discriminant]
  ring

/-- Second-axis form of the same ordered factorization. -/
theorem secondAxisConnectingQuartic_factor
    {R : Type u} [Field R] (a : Coefficients R) (Y : R) :
    characterConicQuartic
        (-traceLinearCoefficient2 a)
        (-traceLinearCoefficient3 a)
        (-traceLinearCoefficient1 a)
        (-traceConstant a) Y =
      (Y + a.a2) ^ 2 * centeredNorm a.a3 a.a1 Y := by
  simp only [characterConicQuartic, traceLinearCoefficient1,
    traceLinearCoefficient2, traceLinearCoefficient3, traceConstant,
    centeredNorm, discriminant]
  ring

/-- Third-axis form of the same ordered factorization. -/
theorem thirdAxisConnectingQuartic_factor
    {R : Type u} [Field R] (a : Coefficients R) (Z : R) :
    characterConicQuartic
        (-traceLinearCoefficient3 a)
        (-traceLinearCoefficient1 a)
        (-traceLinearCoefficient2 a)
        (-traceConstant a) Z =
      (Z + a.a3) ^ 2 * centeredNorm a.a1 a.a2 Z := by
  simp only [characterConicQuartic, traceLinearCoefficient1,
    traceLinearCoefficient2, traceLinearCoefficient3, traceConstant,
    centeredNorm, discriminant]
  ring

/-- Scalar discriminant of the residual centered-norm quadratic. -/
def centeredNormQuadraticDiscriminant
    {R : Type u} [CommRing R] (B C : R) : R :=
  (B * C) ^ 2 - 4 * (B ^ 2 + C ^ 2 - 4)

/-- The residual quadratic is separable precisely away from the two
coefficient degeneracy factors (in odd characteristic). -/
theorem centeredNormQuadraticDiscriminant_factor
    {R : Type u} [CommRing R] (B C : R) :
    centeredNormQuadraticDiscriminant B C =
      (B ^ 2 - 4) * (C ^ 2 - 4) := by
  simp only [centeredNormQuadraticDiscriminant]
  ring

/-- Generic admissibility of the two moving coefficients makes the residual
quadratic discriminant nonzero. -/
theorem centeredNormQuadraticDiscriminant_ne_zero
    {K : Type u} [Field K] (B C : K)
    (hB : B ^ 2 ≠ 4) (hC : C ^ 2 ≠ 4) :
    centeredNormQuadraticDiscriminant B C ≠ 0 := by
  rw [centeredNormQuadraticDiscriminant_factor]
  exact mul_ne_zero (sub_ne_zero.mpr hB) (sub_ne_zero.mpr hC)

/-- Multiplication by a nonzero square does not change square class. -/
theorem isSquare_sq_mul_iff
    {K : Type u} [Field K] (c x : K) (hc : c ≠ 0) :
    IsSquare (c ^ 2 * x) ↔ IsSquare x := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r / c, ?_⟩
    calc
      x = (c ^ 2 * x) / c ^ 2 := by field_simp [hc]
      _ = (r * r) / c ^ 2 := by rw [hr]
      _ = (r / c) * (r / c) := by field_simp [hc]
  · intro hx
    exact (IsSquare.sq c).mul hx

/-- On the candidate-regular first-axis locus, the paper's quartic and the
existing centered norm have exactly the same square class. -/
theorem firstAxisConnectingQuartic_isSquare_iff
    {K : Type u} [Field K] (a : Coefficients K) (X : K)
    (hX : X + a.a1 ≠ 0) :
    IsSquare (firstAxisConnectingQuartic a X) ↔
      IsSquare (centeredNorm a.a2 a.a3 X) := by
  rw [firstAxisConnectingQuartic_factor]
  exact isSquare_sq_mul_iff (X + a.a1)
    (centeredNorm a.a2 a.a3 X) hX

/-- The torus product and centered norm have the same square class whenever
the original coordinate and the nonparabolic discriminant are nonzero. -/
theorem centeredFiberProduct_isSquare_iff_centeredNorm
    {K : Type u} [Field K] (B C u t : K)
    (hu : u ≠ 0) (hD : discriminant t ≠ 0) :
    IsSquare (centeredFiberProduct B C u t) ↔
      IsSquare (centeredNorm B C t) := by
  have hrewrite :
      centeredFiberProduct B C u t =
        (u / discriminant t) ^ 2 * centeredNorm B C t := by
    simp only [centeredFiberProduct]
    field_simp [hD]
  rw [hrewrite]
  exact isSquare_sq_mul_iff
    (u / discriminant t) (centeredNorm B C t)
      (div_ne_zero hu hD)

/-- Consequently, on a regular first-coordinate fiber, nonsquareness of the
character quartic is the exact nonsquareness condition for the torus product
used by the existing Vieta-reflection formulas. -/
theorem firstAxisConnectingQuartic_not_isSquare_iff_centeredFiberProduct
    {K : Type u} [Field K] (a : Coefficients K) (u t : K)
    (hu : u ≠ 0) (hD : discriminant t ≠ 0)
    (ht : t + a.a1 ≠ 0) :
    (¬ IsSquare (firstAxisConnectingQuartic a t)) ↔
      ¬ IsSquare (centeredFiberProduct a.a2 a.a3 u t) := by
  rw [firstAxisConnectingQuartic_isSquare_iff a t ht]
  rw [centeredFiberProduct_isSquare_iff_centeredNorm
    a.a2 a.a3 u t hu hD]

end

end GenMarkoff.General.Cage
