import GenMarkoff.Core.Basic

/-!
# Regular angle identities

This file formalizes the three functions `Δᵢ` introduced in
arXiv:2509.02187v3, equation (14).  Lean's division is total, so the functions
are defined on every point; the identities below state precisely the
nonvanishing hypotheses under which the displayed rational formulas have
their intended meaning.

The coefficient `1 / 2` forces the field to have characteristic different
from two.  The Vieta-pair identities need only the two coordinates unchanged
by the corresponding Vieta move, and do not require the surface equation.
-/

namespace GenMarkoff

universe u

section Field

variable {K : Type u} [Field K]

/-- The first raw angle function
`Δ₁(x) = x₁/(x₃x₂) + (a₃/x₃ + a₂/x₂)/2`. -/
def rawAngle1 (a : Coefficients K) (x : Point K) : K :=
  x.x1 / (x.x3 * x.x2) + (a.a3 / x.x3 + a.a2 / x.x2) / 2

/-- The second raw angle function
`Δ₂(x) = x₂/(x₁x₃) + (a₁/x₁ + a₃/x₃)/2`. -/
def rawAngle2 (a : Coefficients K) (x : Point K) : K :=
  x.x2 / (x.x1 * x.x3) + (a.a1 / x.x1 + a.a3 / x.x3) / 2

/-- The third raw angle function
`Δ₃(x) = x₃/(x₂x₁) + (a₂/x₂ + a₁/x₁)/2`. -/
def rawAngle3 (a : Coefficients K) (x : Point K) : K :=
  x.x3 / (x.x2 * x.x1) + (a.a2 / x.x2 + a.a1 / x.x1) / 2

/-- On an all-nonzero solution, the three raw angles sum to the cubic
multiplier `s = 3 + a₁ + a₂ + a₃`. -/
theorem rawAngle_total (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx1 : x.x1 ≠ 0) (hx2 : x.x2 ≠ 0) (hx3 : x.x3 ≠ 0)
    (hx : IsSolution a x) :
    rawAngle1 a x + rawAngle2 a x + rawAngle3 a x = a.multiplier := by
  unfold rawAngle1 rawAngle2 rawAngle3 Coefficients.multiplier
  rw [IsSolution, polynomial] at hx
  unfold Coefficients.multiplier at hx
  field_simp [h2, hx1, hx2, hx3]
  linear_combination 2 * hx

/-- Pairing the first raw angle with the first Vieta involution gives `s`.
Only `x₂` and `x₃`, the unchanged coordinates, need to be nonzero. -/
theorem rawAngle1_add_vieta1 (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx2 : x.x2 ≠ 0) (hx3 : x.x3 ≠ 0) :
    rawAngle1 a x + rawAngle1 a (vieta1 a x) = a.multiplier := by
  unfold rawAngle1 vieta1 Coefficients.multiplier
  field_simp [h2, hx2, hx3]
  ring

/-- Pairing the second raw angle with the second Vieta involution gives `s`.
Only `x₁` and `x₃`, the unchanged coordinates, need to be nonzero. -/
theorem rawAngle2_add_vieta2 (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx1 : x.x1 ≠ 0) (hx3 : x.x3 ≠ 0) :
    rawAngle2 a x + rawAngle2 a (vieta2 a x) = a.multiplier := by
  unfold rawAngle2 vieta2 Coefficients.multiplier
  field_simp [h2, hx1, hx3]
  ring

/-- Pairing the third raw angle with the third Vieta involution gives `s`.
Only `x₁` and `x₂`, the unchanged coordinates, need to be nonzero. -/
theorem rawAngle3_add_vieta3 (a : Coefficients K) (x : Point K)
    (h2 : (2 : K) ≠ 0) (hx1 : x.x1 ≠ 0) (hx2 : x.x2 ≠ 0) :
    rawAngle3 a x + rawAngle3 a (vieta3 a x) = a.multiplier := by
  unfold rawAngle3 vieta3 Coefficients.multiplier
  field_simp [h2, hx1, hx2]
  ring

/-- On the punctured surface, if `x₁ = 0`, then the other two coordinates are
both nonzero. -/
theorem coordinates_ne_zero_of_x1_eq_zero (a : Coefficients K) (x : Point K)
    (hx : IsSolution a x) (hpunctured : x ≠ origin) (hx1 : x.x1 = 0) :
    x.x2 ≠ 0 ∧ x.x3 ≠ 0 := by
  rw [IsSolution, polynomial] at hx
  constructor
  · intro hx2
    apply hpunctured
    ext
    · exact hx1
    · exact hx2
    · have hx3sq : x.x3 ^ 2 = 0 := by
        simpa [hx1, hx2] using hx
      exact sq_eq_zero_iff.mp hx3sq
  · intro hx3
    apply hpunctured
    ext
    · exact hx1
    · have hx2sq : x.x2 ^ 2 = 0 := by
        simpa [hx1, hx3] using hx
      exact sq_eq_zero_iff.mp hx2sq
    · exact hx3

/-- If `x₁ = 0` on the punctured surface, the ratio `x₂/x₃` is a root of
`T² + a₁T + 1`. -/
theorem ratio_quadratic_of_x1_eq_zero (a : Coefficients K) (x : Point K)
    (hx : IsSolution a x) (hpunctured : x ≠ origin) (hx1 : x.x1 = 0) :
    (x.x2 / x.x3) ^ 2 + a.a1 * (x.x2 / x.x3) + 1 = 0 := by
  have hne := coordinates_ne_zero_of_x1_eq_zero a x hx hpunctured hx1
  rw [IsSolution, polynomial] at hx
  field_simp [hne.2]
  rw [hx1] at hx
  linear_combination hx

/-- On the punctured surface, if `x₂ = 0`, then the other two coordinates are
both nonzero.  This is proved directly on the fixed coefficient surface. -/
theorem coordinates_ne_zero_of_x2_eq_zero (a : Coefficients K) (x : Point K)
    (hx : IsSolution a x) (hpunctured : x ≠ origin) (hx2 : x.x2 = 0) :
    x.x1 ≠ 0 ∧ x.x3 ≠ 0 := by
  rw [IsSolution, polynomial] at hx
  constructor
  · intro hx1
    apply hpunctured
    ext
    · exact hx1
    · exact hx2
    · have hx3sq : x.x3 ^ 2 = 0 := by
        simpa [hx1, hx2] using hx
      exact sq_eq_zero_iff.mp hx3sq
  · intro hx3
    apply hpunctured
    ext
    · have hx1sq : x.x1 ^ 2 = 0 := by
        simpa [hx2, hx3] using hx
      exact sq_eq_zero_iff.mp hx1sq
    · exact hx2
    · exact hx3

/-- If `x₂ = 0` on the punctured surface, the cyclic ratio `x₃/x₁` is a root
of `T² + a₂T + 1`. -/
theorem ratio_quadratic_of_x2_eq_zero (a : Coefficients K) (x : Point K)
    (hx : IsSolution a x) (hpunctured : x ≠ origin) (hx2 : x.x2 = 0) :
    (x.x3 / x.x1) ^ 2 + a.a2 * (x.x3 / x.x1) + 1 = 0 := by
  have hne := coordinates_ne_zero_of_x2_eq_zero a x hx hpunctured hx2
  rw [IsSolution, polynomial] at hx
  field_simp [hne.1]
  rw [hx2] at hx
  linear_combination hx

/-- On the punctured surface, if `x₃ = 0`, then the other two coordinates are
both nonzero.  This is proved directly on the fixed coefficient surface. -/
theorem coordinates_ne_zero_of_x3_eq_zero (a : Coefficients K) (x : Point K)
    (hx : IsSolution a x) (hpunctured : x ≠ origin) (hx3 : x.x3 = 0) :
    x.x1 ≠ 0 ∧ x.x2 ≠ 0 := by
  rw [IsSolution, polynomial] at hx
  constructor
  · intro hx1
    apply hpunctured
    ext
    · exact hx1
    · have hx2sq : x.x2 ^ 2 = 0 := by
        simpa [hx1, hx3] using hx
      exact sq_eq_zero_iff.mp hx2sq
    · exact hx3
  · intro hx2
    apply hpunctured
    ext
    · have hx1sq : x.x1 ^ 2 = 0 := by
        simpa [hx2, hx3] using hx
      exact sq_eq_zero_iff.mp hx1sq
    · exact hx2
    · exact hx3

/-- If `x₃ = 0` on the punctured surface, the cyclic ratio `x₁/x₂` is a root
of `T² + a₃T + 1`. -/
theorem ratio_quadratic_of_x3_eq_zero (a : Coefficients K) (x : Point K)
    (hx : IsSolution a x) (hpunctured : x ≠ origin) (hx3 : x.x3 = 0) :
    (x.x1 / x.x2) ^ 2 + a.a3 * (x.x1 / x.x2) + 1 = 0 := by
  have hne := coordinates_ne_zero_of_x3_eq_zero a x hx hpunctured hx3
  rw [IsSolution, polynomial] at hx
  field_simp [hne.2]
  rw [hx3] at hx
  linear_combination hx

/-- Suppose `x₁ = 0` and put `r = x₂ / x₃`.  For the repository's
right-to-left composition convention `rotation1 = vieta3 ∘ vieta2`, the
first raw angle scales by `r²` in one step.  The quadratic hypothesis is
exactly the conclusion of `ratio_quadratic_of_x1_eq_zero` on the punctured
surface.

Equivalently, the two nonzero coordinates scale by `r⁻²`; this explains why
the reciprocal raw angle has the displayed `r²` factor. -/
theorem rawAngle1_rotation1_scale_of_x1_eq_zero (a : Coefficients K) (x : Point K)
    (hx1 : x.x1 = 0) (hx2 : x.x2 ≠ 0) (hx3 : x.x3 ≠ 0)
    (hratio : (x.x2 / x.x3) ^ 2 + a.a1 * (x.x2 / x.x3) + 1 = 0) :
    rawAngle1 a (rotation1 a x) =
      (x.x2 / x.x3) ^ 2 * rawAngle1 a x := by
  have hquad : x.x2 ^ 2 + a.a1 * x.x2 * x.x3 + x.x3 ^ 2 = 0 := by
    field_simp [hx3] at hratio
    linear_combination hratio
  have hrot2 : (rotation1 a x).x2 = x.x3 ^ 2 / x.x2 := by
    unfold rotation1 vieta3 vieta2
    dsimp
    rw [hx1]
    field_simp [hx2]
    linear_combination -hquad
  have hrot3 : (rotation1 a x).x3 = x.x3 ^ 3 / x.x2 ^ 2 := by
    have hformula :
        (rotation1 a x).x3 = -x.x3 - a.a1 * (rotation1 a x).x2 := by
      simp [rotation1, vieta3, vieta2, hx1]
    rw [hformula, hrot2]
    field_simp [hx2]
    linear_combination -hquad
  have hrot1 : (rotation1 a x).x1 = 0 := by
    simp [rotation1, vieta3, vieta2, hx1]
  unfold rawAngle1
  rw [hrot1, hrot2, hrot3, hx1]
  field_simp [hx2, hx3]
  ring

/-- Cyclic second-coordinate version of
`rawAngle1_rotation1_scale_of_x1_eq_zero`.  With `x₂ = 0` and
`r = x₃ / x₁`, the actual fixed-coefficient rotation
`rotation2 = vieta1 ∘ vieta3` scales the second raw angle by `r²`. -/
theorem rawAngle2_rotation2_scale_of_x2_eq_zero (a : Coefficients K) (x : Point K)
    (hx2 : x.x2 = 0) (hx1 : x.x1 ≠ 0) (hx3 : x.x3 ≠ 0)
    (hratio : (x.x3 / x.x1) ^ 2 + a.a2 * (x.x3 / x.x1) + 1 = 0) :
    rawAngle2 a (rotation2 a x) =
      (x.x3 / x.x1) ^ 2 * rawAngle2 a x := by
  have hquad : x.x3 ^ 2 + a.a2 * x.x3 * x.x1 + x.x1 ^ 2 = 0 := by
    field_simp [hx1] at hratio
    linear_combination hratio
  have hrot3 : (rotation2 a x).x3 = x.x1 ^ 2 / x.x3 := by
    unfold rotation2 vieta1 vieta3
    dsimp
    rw [hx2]
    field_simp [hx3]
    linear_combination -hquad
  have hrot1 : (rotation2 a x).x1 = x.x1 ^ 3 / x.x3 ^ 2 := by
    have hformula :
        (rotation2 a x).x1 = -x.x1 - a.a2 * (rotation2 a x).x3 := by
      simp [rotation2, vieta1, vieta3, hx2]
    rw [hformula, hrot3]
    field_simp [hx3]
    linear_combination -hquad
  have hrot2 : (rotation2 a x).x2 = 0 := by
    simp [rotation2, vieta1, vieta3, hx2]
  unfold rawAngle2
  rw [hrot2, hrot1, hrot3, hx2]
  field_simp [hx1, hx3]
  ring

/-- Cyclic third-coordinate version of
`rawAngle1_rotation1_scale_of_x1_eq_zero`.  With `x₃ = 0` and
`r = x₁ / x₂`, the actual fixed-coefficient rotation
`rotation3 = vieta2 ∘ vieta1` scales the third raw angle by `r²`. -/
theorem rawAngle3_rotation3_scale_of_x3_eq_zero (a : Coefficients K) (x : Point K)
    (hx3 : x.x3 = 0) (hx1 : x.x1 ≠ 0) (hx2 : x.x2 ≠ 0)
    (hratio : (x.x1 / x.x2) ^ 2 + a.a3 * (x.x1 / x.x2) + 1 = 0) :
    rawAngle3 a (rotation3 a x) =
      (x.x1 / x.x2) ^ 2 * rawAngle3 a x := by
  have hquad : x.x1 ^ 2 + a.a3 * x.x1 * x.x2 + x.x2 ^ 2 = 0 := by
    field_simp [hx2] at hratio
    linear_combination hratio
  have hrot1 : (rotation3 a x).x1 = x.x2 ^ 2 / x.x1 := by
    unfold rotation3 vieta2 vieta1
    dsimp
    rw [hx3]
    field_simp [hx1]
    linear_combination -hquad
  have hrot2 : (rotation3 a x).x2 = x.x2 ^ 3 / x.x1 ^ 2 := by
    have hformula :
        (rotation3 a x).x2 = -x.x2 - a.a3 * (rotation3 a x).x1 := by
      simp [rotation3, vieta2, vieta1, hx3]
    rw [hformula, hrot1]
    field_simp [hx1]
    linear_combination -hquad
  have hrot3 : (rotation3 a x).x3 = 0 := by
    simp [rotation3, vieta2, vieta1, hx3]
  unfold rawAngle3
  rw [hrot3, hrot2, hrot1, hx3]
  field_simp [hx1, hx2]
  ring

end Field

end GenMarkoff
