import GenMarkoff.Core.Statements

/-!
# Affine fiber dynamics for a fixed coefficient triple

For an ordered coefficient frame `(A, B, C)`, fix the coordinate carrying
`A`, write its value as `u`, and put `t = s * u - A`, where `s` is the
surface multiplier.  On the ordered pair of moving coordinates the two
Vieta factors are

`T_c(y, z) = (z, t * z - y - c * u)`.

The rotation is the heterogeneous composition `T_B ∘ T_C`.  Its linear part
is the square of the usual trace matrix, but its translation is not the
square translation unless `B = C`.

All three fixed-coordinate identities are stated explicitly.  They cyclically
relabel the ordered frame while leaving the coefficient triple itself fixed.
-/

namespace GenMarkoff.General

universe u

open scoped Matrix

section Ring

variable {R : Type u} [CommRing R]

/-- The trace attached to a fixed coordinate in an ordered coefficient
frame. -/
def orderedTrace (s A u : R) : R :=
  s * u - A

/-- The common linear part of an affine Vieta half-step. -/
def linearStep (t : R) (v : R × R) : R × R :=
  (v.2, t * v.2 - v.1)

/-- The affine step with translation coefficient `c`. -/
def affineStep (c u t : R) (v : R × R) : R × R :=
  (v.2, t * v.2 - v.1 - c * u)

/-- The rotation on an ordered fiber: first apply the `C` step and then the
`B` step. -/
def affineRotation (B C u t : R) (v : R × R) : R × R :=
  affineStep B u t (affineStep C u t v)

/-- Moving coordinates for the rotation fixing the first coordinate. -/
def movingCoordinates1 (x : Point R) : R × R :=
  (x.x2, x.x3)

/-- Moving coordinates for the rotation fixing the second coordinate. -/
def movingCoordinates2 (x : Point R) : R × R :=
  (x.x3, x.x1)

/-- Moving coordinates for the rotation fixing the third coordinate. -/
def movingCoordinates3 (x : Point R) : R × R :=
  (x.x1, x.x2)

/-- Explicit formula for the heterogeneous affine composition. -/
theorem affineRotation_apply (B C u t : R) (v : R × R) :
    affineRotation B C u t v =
      (t * v.2 - v.1 - C * u,
        (t ^ 2 - 1) * v.2 - t * v.1 - (t * C + B) * u) := by
  ext
  · simp [affineRotation, affineStep]
  · simp [affineRotation, affineStep]
    ring

/-- The first rotation is `T_{a₂} ∘ T_{a₃}` on `(x₂,x₃)`. -/
theorem movingCoordinates1_rotation1 (a : Coefficients R) (x : Point R) :
    movingCoordinates1 (rotation1 a x) =
      affineRotation a.a2 a.a3 x.x1
        (orderedTrace a.multiplier a.a1 x.x1) (movingCoordinates1 x) := by
  ext <;>
    simp [movingCoordinates1, rotation1, vieta2, vieta3, affineRotation,
      affineStep, orderedTrace] <;>
    ring

/-- The second rotation is `T_{a₃} ∘ T_{a₁}` on `(x₃,x₁)`. -/
theorem movingCoordinates2_rotation2 (a : Coefficients R) (x : Point R) :
    movingCoordinates2 (rotation2 a x) =
      affineRotation a.a3 a.a1 x.x2
        (orderedTrace a.multiplier a.a2 x.x2) (movingCoordinates2 x) := by
  ext <;>
    simp [movingCoordinates2, rotation2, vieta1, vieta3, affineRotation,
      affineStep, orderedTrace] <;>
    ring

/-- The third rotation is `T_{a₁} ∘ T_{a₂}` on `(x₁,x₂)`. -/
theorem movingCoordinates3_rotation3 (a : Coefficients R) (x : Point R) :
    movingCoordinates3 (rotation3 a x) =
      affineRotation a.a1 a.a2 x.x3
        (orderedTrace a.multiplier a.a3 x.x3) (movingCoordinates3 x) := by
  ext <;>
    simp [movingCoordinates3, rotation3, vieta1, vieta2, affineRotation,
      affineStep, orderedTrace] <;>
    ring

/-- Explicit square of the common linear half-step. -/
theorem linearStep_sq (t : R) (v : R × R) :
    linearStep t (linearStep t v) =
      (t * v.2 - v.1, (t ^ 2 - 1) * v.2 - t * v.1) := by
  ext
  · simp [linearStep]
  · simp [linearStep]
    ring

/-- Removing the translation from `affineRotation` leaves the square of the
trace matrix. -/
theorem affineRotation_eq_linearStep_sq_add (B C u t : R) (v : R × R) :
    affineRotation B C u t v =
      let w := linearStep t (linearStep t v)
      (w.1 - C * u, w.2 - (t * C + B) * u) := by
  ext
  · simp [affineRotation, affineStep, linearStep]
  · simp [affineRotation, affineStep, linearStep]
    ring

/-- The matrix of the common linear half-step. -/
def fiberMatrix (t : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; -1, t]

@[simp]
theorem fiberMatrix_det (t : R) : (fiberMatrix t).det = 1 := by
  simp [fiberMatrix, Matrix.det_fin_two_of]

@[simp]
theorem fiberMatrix_trace (t : R) : (fiberMatrix t).trace = t := by
  simp [fiberMatrix, Matrix.trace_fin_two_of]

/-- The trace matrix as an element of `SL₂`. -/
def fiberMatrixSL (t : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨fiberMatrix t, fiberMatrix_det t⟩

/-- The order of the actual rotation linear part. -/
noncomputable def rotationLinearOrder (t : R) : ℕ :=
  orderOf (fiberMatrixSL t ^ 2)

/-- The actual rotation order is the half-step order divided by its parity
factor. -/
theorem rotationLinearOrder_eq_order_div_gcd (t : R) :
    rotationLinearOrder t =
      orderOf (fiberMatrixSL t) / Nat.gcd (orderOf (fiberMatrixSL t)) 2 := by
  exact orderOf_pow' (fiberMatrixSL t) (by norm_num)

/-- The ordered fixed-coordinate conic. -/
def fiberConic (B C u t y z : R) : R :=
  y ^ 2 + z ^ 2 - t * y * z + C * u * y + B * u * z + u ^ 2

/-- The surface equation on the first-coordinate fiber. -/
theorem polynomial_fixed_first (a : Coefficients R) (u y z : R) :
    polynomial a ⟨u, y, z⟩ =
      fiberConic a.a2 a.a3 u
        (orderedTrace a.multiplier a.a1 u) y z := by
  simp [polynomial, fiberConic, orderedTrace]
  ring

/-- The surface equation on the second-coordinate fiber, in moving order
`(x₃,x₁)`. -/
theorem polynomial_fixed_second (a : Coefficients R) (u z x : R) :
    polynomial a ⟨x, u, z⟩ =
      fiberConic a.a3 a.a1 u
        (orderedTrace a.multiplier a.a2 u) z x := by
  simp [polynomial, fiberConic, orderedTrace]
  ring

/-- The surface equation on the third-coordinate fiber, in moving order
`(x₁,x₂)`. -/
theorem polynomial_fixed_third (a : Coefficients R) (u x y : R) :
    polynomial a ⟨x, y, u⟩ =
      fiberConic a.a1 a.a2 u
        (orderedTrace a.multiplier a.a3 u) x y := by
  simp [polynomial, fiberConic, orderedTrace]
  ring

end Ring

section Field

variable {K : Type u} [Field K]

/-- The nonparabolic discriminant. -/
def discriminant (t : K) : K :=
  t ^ 2 - 4

/-- The numerator of the centered-conic constant. -/
def centeredNorm (B C t : K) : K :=
  discriminant t + B ^ 2 + C ^ 2 + t * B * C

/-- The ordered affine center of `T_B ∘ T_C`. -/
def fiberCenter (B C u t : K) : K × K :=
  (u * (t * B + 2 * C) / discriminant t,
    u * (t * C + 2 * B) / discriminant t)

/-- Translate an ordered moving pair by an ordered center. -/
def centerCoordinates (m v : K × K) : K × K :=
  (v.1 - m.1, v.2 - m.2)

theorem centerCoordinates_injective (m : K × K) :
    Function.Injective (centerCoordinates m) := by
  intro v w h
  apply Prod.ext
  · exact sub_left_injective (congrArg Prod.fst h)
  · exact sub_left_injective (congrArg Prod.snd h)

/-- The displayed center is fixed by the heterogeneous affine rotation. -/
theorem affineRotation_fiberCenter
    (B C u t : K) (hD : discriminant t ≠ 0) :
    affineRotation B C u t (fiberCenter B C u t) =
      fiberCenter B C u t := by
  rw [affineRotation_apply]
  apply Prod.ext
  · change
      t * (u * (t * C + 2 * B) / discriminant t) -
          u * (t * B + 2 * C) / discriminant t - C * u =
        u * (t * B + 2 * C) / discriminant t
    field_simp [hD]
    simp only [discriminant]
    ring
  · change
      (t ^ 2 - 1) * (u * (t * C + 2 * B) / discriminant t) -
            t * (u * (t * B + 2 * C) / discriminant t) -
          (t * C + B) * u =
        u * (t * C + 2 * B) / discriminant t
    field_simp [hD]
    simp only [discriminant]
    ring

/-- Centering conjugates the heterogeneous affine rotation to the square of
the common linear trace step. -/
theorem centerCoordinates_affineRotation
    (B C u t : K) (v : K × K) (hD : discriminant t ≠ 0) :
    centerCoordinates (fiberCenter B C u t)
        (affineRotation B C u t v) =
      linearStep t (linearStep t
        (centerCoordinates (fiberCenter B C u t) v)) := by
  rw [affineRotation_apply]
  apply Prod.ext
  · change
      t * v.2 - v.1 - C * u -
          u * (t * B + 2 * C) / discriminant t =
        t * (v.2 - u * (t * C + 2 * B) / discriminant t) -
          (v.1 - u * (t * B + 2 * C) / discriminant t)
    field_simp [hD]
    simp only [discriminant]
    ring
  · change
      (t ^ 2 - 1) * v.2 - t * v.1 - (t * C + B) * u -
          u * (t * C + 2 * B) / discriminant t =
        t *
            (t * (v.2 - u * (t * C + 2 * B) / discriminant t) -
              (v.1 - u * (t * B + 2 * C) / discriminant t)) -
          (v.2 - u * (t * C + 2 * B) / discriminant t)
    field_simp [hD]
    simp only [discriminant]
    ring

/-- The centered form of the ordered affine conic. -/
theorem fiberConic_centered
    (B C u t Y Z : K) (hD : discriminant t ≠ 0) :
    fiberConic B C u t
        (Y + (fiberCenter B C u t).1)
        (Z + (fiberCenter B C u t).2) =
      Y ^ 2 + Z ^ 2 - t * Y * Z +
        u ^ 2 * centeredNorm B C t / discriminant t := by
  change
    (Y + u * (t * B + 2 * C) / discriminant t) ^ 2 +
          (Z + u * (t * C + 2 * B) / discriminant t) ^ 2 -
        t * (Y + u * (t * B + 2 * C) / discriminant t) *
          (Z + u * (t * C + 2 * B) / discriminant t) +
      C * u * (Y + u * (t * B + 2 * C) / discriminant t) +
      B * u * (Z + u * (t * C + 2 * B) / discriminant t) + u ^ 2 =
    Y ^ 2 + Z ^ 2 - t * Y * Z +
      u ^ 2 *
          (discriminant t + B ^ 2 + C ^ 2 + t * B * C) /
        discriminant t
  field_simp [hD]
  simp only [discriminant]
  ring

/-- The product parameter in the standard torus parametrization of the
centered conic. -/
def centeredFiberProduct (B C u t : K) : K :=
  u ^ 2 * centeredNorm B C t / discriminant t ^ 2

/-- The centered conic constant is `discriminant * centeredFiberProduct`. -/
theorem discriminant_mul_centeredFiberProduct
    (B C u t : K) (hD : discriminant t ≠ 0) :
    discriminant t * centeredFiberProduct B C u t =
      u ^ 2 * centeredNorm B C t / discriminant t := by
  simp [centeredFiberProduct]
  field_simp [hD]

end Field

end GenMarkoff.General
