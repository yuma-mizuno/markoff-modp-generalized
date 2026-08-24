import GenMarkoff.Symmetric.Basic

/-!
# Affine fiber dynamics in the equal-coefficient family

For equal coefficients, the two affine factors of each rotation have the
same translation term.  Consequently the original rotation is the square of
one affine half-step.  We record both orders: the half-step controls the
selected symmetric one-step action, while its square controls the smaller
rotation-group action.
-/

namespace GenMarkoff.Symmetric

universe u

open scoped Matrix

section Ring

variable {R : Type u} [CommRing R]

/-- The linear half-step `(y,z) ↦ (z,tz-y)`. -/
def linearStep (t : R) (v : R × R) : R × R :=
  (v.2, t * v.2 - v.1)

/-- The affine half-step on a fixed-coordinate fiber. -/
def affineStep (c u t : R) (v : R × R) : R × R :=
  (v.2, t * v.2 - v.1 - c * u)

/-- The actual affine half-step, with `t = 3(1+c)u-c`. -/
def fiberStep (c u : R) : R × R → R × R :=
  affineStep c u (trace c u)

/-- Moving coordinates for the rotation fixing the first coordinate. -/
def movingCoordinates1 (x : Point R) : R × R :=
  (x.x2, x.x3)

/-- Moving coordinates for the rotation fixing the second coordinate. -/
def movingCoordinates2 (x : Point R) : R × R :=
  (x.x3, x.x1)

/-- Moving coordinates for the rotation fixing the third coordinate. -/
def movingCoordinates3 (x : Point R) : R × R :=
  (x.x1, x.x2)

/-- In the equal-coefficient family, `R₁ = μ₃ μ₂` is the square of one
affine half-step on the moving pair `(x₂,x₃)`. -/
theorem movingCoordinates1_rotation1 (c : R) (x : Point R) :
    movingCoordinates1 (rotation1 (coefficients c) x) =
      fiberStep c x.x1 (fiberStep c x.x1 (movingCoordinates1 x)) := by
  ext <;>
    simp [movingCoordinates1, rotation1, vieta2, vieta3, fiberStep,
      affineStep, trace, multiplier, coefficients, Coefficients.multiplier] <;>
    ring

/-- Cyclic version of `movingCoordinates1_rotation1` on `(x₃,x₁)`. -/
theorem movingCoordinates2_rotation2 (c : R) (x : Point R) :
    movingCoordinates2 (rotation2 (coefficients c) x) =
      fiberStep c x.x2 (fiberStep c x.x2 (movingCoordinates2 x)) := by
  ext <;>
    simp [movingCoordinates2, rotation2, vieta1, vieta3, fiberStep,
      affineStep, trace, multiplier, coefficients, Coefficients.multiplier] <;>
    ring

/-- Cyclic version of `movingCoordinates1_rotation1` on `(x₁,x₂)`. -/
theorem movingCoordinates3_rotation3 (c : R) (x : Point R) :
    movingCoordinates3 (rotation3 (coefficients c) x) =
      fiberStep c x.x3 (fiberStep c x.x3 (movingCoordinates3 x)) := by
  ext <;>
    simp [movingCoordinates3, rotation3, vieta1, vieta2, fiberStep,
      affineStep, trace, multiplier, coefficients, Coefficients.multiplier] <;>
    ring

/-- Explicit square of the linear half-step. -/
theorem linearStep_sq (t : R) (v : R × R) :
    linearStep t (linearStep t v) =
      (t * v.2 - v.1, (t ^ 2 - 1) * v.2 - t * v.1) := by
  ext <;> simp [linearStep] ; ring

/-- The matrix of the affine half-step's linear part. -/
def fiberMatrix (t : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; -1, t]

@[simp]
theorem fiberMatrix_det (t : R) : (fiberMatrix t).det = 1 := by
  simp [fiberMatrix, Matrix.det_fin_two_of]

@[simp]
theorem fiberMatrix_trace (t : R) : (fiberMatrix t).trace = t := by
  simp [fiberMatrix, Matrix.trace_fin_two_of]

/-- The half-step matrix as an element of `SL₂`. -/
def fiberMatrixSL (t : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨fiberMatrix t, fiberMatrix_det t⟩

/-- The order relevant to the project's rotation generator is the order of
the square of the half-step matrix. -/
noncomputable def squaredRotationOrder (t : R) : ℕ :=
  orderOf (fiberMatrixSL t ^ 2)

/-- The half-step order, recorded only to state the exact parity relation. -/
noncomputable def halfStepOrder (t : R) : ℕ :=
  orderOf (fiberMatrixSL t)

theorem squaredRotationOrder_eq_halfStepOrder_div_gcd (t : R) :
    squaredRotationOrder t = halfStepOrder t / Nat.gcd (halfStepOrder t) 2 := by
  exact orderOf_pow' (fiberMatrixSL t) (by norm_num)

end Ring

section Field

variable {K : Type u} [Field K]

/-- The unique affine center away from the eigenvalue `1` of the half-step. -/
def fiberCenter (c u t : K) : K :=
  c * u / (t - 2)

/-- Translate both moving coordinates by the affine center. -/
def centerCoordinates (m : K) (v : K × K) : K × K :=
  (v.1 - m, v.2 - m)

theorem centerCoordinates_injective (m : K) :
    Function.Injective (centerCoordinates m) := by
  intro v w h
  apply Prod.ext
  · exact sub_left_injective (congrArg Prod.fst h)
  · exact sub_left_injective (congrArg Prod.snd h)

/-- Centering conjugates the affine half-step to its linear part. -/
theorem centerCoordinates_affineStep
    (c u t : K) (v : K × K) (ht : t ≠ 2) :
    centerCoordinates (fiberCenter c u t) (affineStep c u t v) =
      linearStep t (centerCoordinates (fiberCenter c u t) v) := by
  ext <;>
    simp [centerCoordinates, fiberCenter, affineStep, linearStep] ;
    field_simp [sub_ne_zero.mpr ht] ;
    ring

/-- The same conjugacy for the square, which is the actual rotation. -/
theorem centerCoordinates_affineStep_sq
    (c u t : K) (v : K × K) (ht : t ≠ 2) :
    centerCoordinates (fiberCenter c u t)
        (affineStep c u t (affineStep c u t v)) =
      linearStep t (linearStep t
        (centerCoordinates (fiberCenter c u t) v)) := by
  rw [centerCoordinates_affineStep c u t _ ht,
    centerCoordinates_affineStep c u t v ht]

/-- The centered form of the first-coordinate conic. -/
theorem polynomial_centered_fixed_first
    (c u t Y Z : K) (htrace : t = trace c u) (ht : t ≠ 2) :
    polynomial (coefficients c)
        ⟨u, Y + fiberCenter c u t, Z + fiberCenter c u t⟩ =
      Y ^ 2 + Z ^ 2 - t * Y * Z +
        u ^ 2 * (t + c ^ 2 - 2) / (t - 2) := by
  rw [polynomial_fixed_first]
  rw [← htrace]
  simp only [fiberCenter]
  field_simp [sub_ne_zero.mpr ht]
  ring

end Field

end GenMarkoff.Symmetric
