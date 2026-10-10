import GenMarkoff.General.Cage.OrbitCosetBiquadratic
import GenMarkoff.General.Cage.Connecting.PulledRadicands

/-!
# Pulled radicands for an orbit connecting coset

For a split-torus power trace

`T = t^d + t⁻ᵈ`,

this file clears the reciprocal denominators in the orbit discriminant

`(T - gamma)^2 - 4 * alpha * beta`

and in the two component factors

`alpha * ((T - gamma) + 2 * k)`,
`alpha * ((T - gamma) - 2 * k)`.

The pulled orbit discriminant is the reciprocal polynomial

`X^(4d) - 2 * gamma * X^(3d) + (gamma^2 + 2 - 4 * alpha * beta) * X^(2d)
  - 2 * gamma * X^d + 1`.

The two pulled component factors have degree at most `2d`,
with equality when `d > 0` and `alpha ≠ 0`, and when `alpha * beta = k ^ 2`
their product is `alpha ^ 2` times the pulled orbit discriminant
(`orbitComponentPulledRadicands_mul_eq_discriminant`).
-/

namespace GenMarkoff.General.Cage

open BGS.Markoff Polynomial

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The component radicand with the sign opposite to
`orbitComponentRadicand`. -/
def orbitOppositeComponentRadicand
    (alpha k U : K) : K :=
  alpha * (U - 2 * k)

/-- Reciprocal quadratic for
`alpha * ((T - gamma) + 2 * k)`. -/
def orbitComponentPlusReciprocalQuadratic
    (alpha gamma k u : K) : K :=
  alpha * u ^ 2 +
    (alpha * (2 * k - gamma)) * u +
    alpha

/-- Reciprocal quadratic for
`alpha * ((T - gamma) - 2 * k)`. -/
def orbitComponentMinusReciprocalQuadratic
    (alpha gamma k u : K) : K :=
  alpha * u ^ 2 +
    (alpha * (-2 * k - gamma)) * u +
    alpha

/-- Pullback of the orbit discriminant along `u = t^d`. -/
def orbitDiscriminantPulledRadicand
    (alpha beta gamma : K) (d : ℕ) : K[X] :=
  X ^ (4 * d) +
    C (-2 * gamma) * X ^ (3 * d) +
    C (gamma ^ 2 + 2 - 4 * alpha * beta) * X ^ (2 * d) +
    C (-2 * gamma) * X ^ d +
    1

/-- Pullback of the positive component factor along `u = t^d`. -/
def orbitComponentPlusPulledRadicand
    (alpha gamma k : K) (d : ℕ) : K[X] :=
  C alpha * X ^ (2 * d) +
    C (alpha * (2 * k - gamma)) * X ^ d +
    C alpha

/-- Pullback of the negative component factor along `u = t^d`. -/
def orbitComponentMinusPulledRadicand
    (alpha gamma k : K) (d : ℕ) : K[X] :=
  C alpha * X ^ (2 * d) +
    C (alpha * (-2 * k - gamma)) * X ^ d +
    C alpha

@[simp]
theorem eval_orbitComponentPlusPulledRadicand
    (alpha gamma k t : K) (d : ℕ) :
    eval t (orbitComponentPlusPulledRadicand alpha gamma k d) =
      orbitComponentPlusReciprocalQuadratic
        alpha gamma k (t ^ d) := by
  simp only [orbitComponentPlusPulledRadicand,
    orbitComponentPlusReciprocalQuadratic, eval_add, eval_mul, eval_C,
    eval_pow, eval_X]
  simp only [← pow_mul]
  ring

@[simp]
theorem eval_orbitComponentMinusPulledRadicand
    (alpha gamma k t : K) (d : ℕ) :
    eval t (orbitComponentMinusPulledRadicand alpha gamma k d) =
      orbitComponentMinusReciprocalQuadratic
        alpha gamma k (t ^ d) := by
  simp only [orbitComponentMinusPulledRadicand,
    orbitComponentMinusReciprocalQuadratic, eval_add, eval_mul, eval_C,
    eval_pow, eval_X]
  simp only [← pow_mul]
  ring

/-- The positive reciprocal quadratic is its denominator-cleared component
factor. -/
theorem orbitComponentPlusReciprocalQuadratic_eq_mul_component
    (alpha gamma k u : K) (hu : u ≠ 0) :
    orbitComponentPlusReciprocalQuadratic alpha gamma k u =
      u * orbitComponentRadicand alpha k (u + u⁻¹ - gamma) := by
  simp only [orbitComponentPlusReciprocalQuadratic,
    orbitComponentRadicand]
  field_simp [hu]
  ring

/-- The negative reciprocal quadratic is its denominator-cleared component
factor. -/
theorem orbitComponentMinusReciprocalQuadratic_eq_mul_component
    (alpha gamma k u : K) (hu : u ≠ 0) :
    orbitComponentMinusReciprocalQuadratic alpha gamma k u =
      u * orbitOppositeComponentRadicand
        alpha k (u + u⁻¹ - gamma) := by
  simp only [orbitComponentMinusReciprocalQuadratic,
    orbitOppositeComponentRadicand]
  field_simp [hu]
  ring

/-- Exact positive-component evaluation at a unit power parameter. -/
theorem eval_orbitComponentPlusPulledRadicand_unit
    (alpha gamma k : K) (t : Kˣ) (d : ℕ) :
    eval (t : K)
        (orbitComponentPlusPulledRadicand alpha gamma k d) =
      (t : K) ^ d *
        orbitComponentRadicand alpha k
          (splitTorusTrace (t ^ d) - gamma) := by
  rw [eval_orbitComponentPlusPulledRadicand,
    orbitComponentPlusReciprocalQuadratic_eq_mul_component
      alpha gamma k ((t : K) ^ d)
        (pow_ne_zero d t.ne_zero)]
  congr 2
  simp [splitTorusTrace]

/-- Exact negative-component evaluation at a unit power parameter. -/
theorem eval_orbitComponentMinusPulledRadicand_unit
    (alpha gamma k : K) (t : Kˣ) (d : ℕ) :
    eval (t : K)
        (orbitComponentMinusPulledRadicand alpha gamma k d) =
      (t : K) ^ d *
        orbitOppositeComponentRadicand alpha k
          (splitTorusTrace (t ^ d) - gamma) := by
  rw [eval_orbitComponentMinusPulledRadicand,
    orbitComponentMinusReciprocalQuadratic_eq_mul_component
      alpha gamma k ((t : K) ^ d)
        (pow_ne_zero d t.ne_zero)]
  congr 2
  simp [splitTorusTrace]

/-- When `alpha * beta = k²`, the two pulled component factors multiply to
`alpha²` times the pulled orbit discriminant. -/
theorem orbitComponentPulledRadicands_mul_eq_discriminant
    (alpha beta gamma k : K) (d : ℕ)
    (hproduct : alpha * beta = k ^ 2) :
    orbitComponentPlusPulledRadicand alpha gamma k d *
        orbitComponentMinusPulledRadicand alpha gamma k d =
      C (alpha ^ 2) *
        orbitDiscriminantPulledRadicand alpha beta gamma d := by
  simp only [orbitComponentPlusPulledRadicand,
    orbitComponentMinusPulledRadicand,
    orbitDiscriminantPulledRadicand]
  have hproduct4 :
      4 * alpha * beta = 4 * k ^ 2 := by
    calc
      4 * alpha * beta = 4 * (alpha * beta) := by ring
      _ = 4 * k ^ 2 := by rw [hproduct]
  rw [hproduct4]
  simp only [map_pow, map_add, map_sub, map_mul, map_neg, map_ofNat]
  ring

/-- The positive component pullback has degree at most `2d`. -/
theorem orbitComponentPlusPulledRadicand_natDegree_le
    (alpha gamma k : K) (d : ℕ) :
    (orbitComponentPlusPulledRadicand alpha gamma k d).natDegree ≤
      2 * d := by
  unfold orbitComponentPlusPulledRadicand
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_C_mul_X_pow_le _ _
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · exact (natDegree_C _).le.trans (Nat.zero_le _)

/-- The negative component pullback has degree at most `2d`. -/
theorem orbitComponentMinusPulledRadicand_natDegree_le
    (alpha gamma k : K) (d : ℕ) :
    (orbitComponentMinusPulledRadicand alpha gamma k d).natDegree ≤
      2 * d := by
  unfold orbitComponentMinusPulledRadicand
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_C_mul_X_pow_le _ _
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · exact (natDegree_C _).le.trans (Nat.zero_le _)

/-- For positive `d`, the coefficient of `X ^ (2 * d)` in the positive
component pullback is `alpha`. -/
theorem coeff_orbitComponentPlusPulledRadicand_two_mul
    (alpha gamma k : K) {d : ℕ} (hd : 0 < d) :
    (orbitComponentPlusPulledRadicand alpha gamma k d).coeff (2 * d) =
      alpha := by
  have hcoeff1 :
      (C (alpha * (2 * k - gamma)) * X ^ d : K[X]).coeff
          (2 * d) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_C_mul_X_pow_le _ _).trans_lt (by omega)
  have hcoeff0 : (C alpha : K[X]).coeff (2 * d) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_C _).le.trans_lt (by omega)
  rw [orbitComponentPlusPulledRadicand]
  simp only [coeff_add, hcoeff1, hcoeff0, add_zero]
  simp

/-- For positive `d`, the coefficient of `X ^ (2 * d)` in the negative
component pullback is `alpha`. -/
theorem coeff_orbitComponentMinusPulledRadicand_two_mul
    (alpha gamma k : K) {d : ℕ} (hd : 0 < d) :
    (orbitComponentMinusPulledRadicand alpha gamma k d).coeff (2 * d) =
      alpha := by
  have hcoeff1 :
      (C (alpha * (-2 * k - gamma)) * X ^ d : K[X]).coeff
          (2 * d) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_C_mul_X_pow_le _ _).trans_lt (by omega)
  have hcoeff0 : (C alpha : K[X]).coeff (2 * d) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_C _).le.trans_lt (by omega)
  rw [orbitComponentMinusPulledRadicand]
  simp only [coeff_add, hcoeff1, hcoeff0, add_zero]
  simp

/-- The `2d` positive-component degree bound is sharp when
`alpha ≠ 0`. -/
theorem orbitComponentPlusPulledRadicand_natDegree_eq
    {alpha : K} (halpha : alpha ≠ 0) (gamma k : K)
    {d : ℕ} (hd : 0 < d) :
    (orbitComponentPlusPulledRadicand alpha gamma k d).natDegree =
      2 * d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact orbitComponentPlusPulledRadicand_natDegree_le
      alpha gamma k d
  · simpa [coeff_orbitComponentPlusPulledRadicand_two_mul
      alpha gamma k hd] using halpha

/-- The `2d` negative-component degree bound is sharp when
`alpha ≠ 0`. -/
theorem orbitComponentMinusPulledRadicand_natDegree_eq
    {alpha : K} (halpha : alpha ≠ 0) (gamma k : K)
    {d : ℕ} (hd : 0 < d) :
    (orbitComponentMinusPulledRadicand alpha gamma k d).natDegree =
      2 * d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact orbitComponentMinusPulledRadicand_natDegree_le
      alpha gamma k d
  · simpa [coeff_orbitComponentMinusPulledRadicand_two_mul
      alpha gamma k hd] using halpha

end

end GenMarkoff.General.Cage
